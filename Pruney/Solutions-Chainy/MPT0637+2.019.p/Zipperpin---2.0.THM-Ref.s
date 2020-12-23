%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pMj6AFPU5N

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:58 EST 2020

% Result     : Theorem 2.46s
% Output     : Refutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  213 (12172 expanded)
%              Number of leaves         :   25 (4086 expanded)
%              Depth                    :   27
%              Number of atoms          : 2020 (104077 expanded)
%              Number of equality atoms :  149 (8830 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('8',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ X19 @ ( k6_relat_1 @ ( k2_relat_1 @ X19 ) ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('15',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('17',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('20',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('21',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['18','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('47',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('57',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','61'])).

thf('63',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('64',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','69'])).

thf('71',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','72'])).

thf('74',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['52','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','76'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('79',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('85',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('86',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( ( k5_relat_1 @ X17 @ ( k6_relat_1 @ X18 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','97'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','97'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('109',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('112',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['107','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('116',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['106','117'])).

thf('119',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['105','120'])).

thf('122',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['123','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['122','129'])).

thf('131',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['121','132','133'])).

thf('135',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('140',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','138','139','140'])).

thf('142',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('143',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['141','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('151',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('153',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['151','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['150','159'])).

thf('161',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['149','160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('164',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['162','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('168',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('169',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['149','160','161'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','138','139','140'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['149','160','161'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['149','160','161'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['149','160','161'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['166','167','168','169','170','173','174','175','176','177'])).

thf('179',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['4','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['166','167','168','169','170','173','174','175','176','177'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['166','167','168','169','170','173','174','175','176','177'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['179','184'])).

thf('186',plain,(
    $false ),
    inference(simplify,[status(thm)],['185'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pMj6AFPU5N
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.46/2.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.46/2.69  % Solved by: fo/fo7.sh
% 2.46/2.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.46/2.69  % done 2353 iterations in 2.231s
% 2.46/2.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.46/2.69  % SZS output start Refutation
% 2.46/2.69  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.46/2.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.46/2.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.46/2.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.46/2.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.46/2.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.46/2.69  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.46/2.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.46/2.69  thf(sk_A_type, type, sk_A: $i).
% 2.46/2.69  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.46/2.69  thf(sk_B_type, type, sk_B: $i).
% 2.46/2.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.46/2.69  thf(t94_relat_1, axiom,
% 2.46/2.69    (![A:$i,B:$i]:
% 2.46/2.69     ( ( v1_relat_1 @ B ) =>
% 2.46/2.69       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.46/2.69  thf('0', plain,
% 2.46/2.69      (![X22 : $i, X23 : $i]:
% 2.46/2.69         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 2.46/2.69          | ~ (v1_relat_1 @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.46/2.69  thf(t43_funct_1, conjecture,
% 2.46/2.69    (![A:$i,B:$i]:
% 2.46/2.69     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.46/2.69       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.46/2.69  thf(zf_stmt_0, negated_conjecture,
% 2.46/2.69    (~( ![A:$i,B:$i]:
% 2.46/2.69        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.46/2.69          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 2.46/2.69    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 2.46/2.69  thf('1', plain,
% 2.46/2.69      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 2.46/2.69         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.46/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.46/2.69  thf('2', plain,
% 2.46/2.69      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.46/2.69          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 2.46/2.69        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['0', '1'])).
% 2.46/2.69  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 2.46/2.69  thf('3', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('4', plain,
% 2.46/2.69      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.46/2.69         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.46/2.69      inference('demod', [status(thm)], ['2', '3'])).
% 2.46/2.69  thf('5', plain,
% 2.46/2.69      (![X22 : $i, X23 : $i]:
% 2.46/2.69         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 2.46/2.69          | ~ (v1_relat_1 @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.46/2.69  thf('6', plain,
% 2.46/2.69      (![X22 : $i, X23 : $i]:
% 2.46/2.69         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 2.46/2.69          | ~ (v1_relat_1 @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.46/2.69  thf('7', plain,
% 2.46/2.69      (![X22 : $i, X23 : $i]:
% 2.46/2.69         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 2.46/2.69          | ~ (v1_relat_1 @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.46/2.69  thf(t80_relat_1, axiom,
% 2.46/2.69    (![A:$i]:
% 2.46/2.69     ( ( v1_relat_1 @ A ) =>
% 2.46/2.69       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.46/2.69  thf('8', plain,
% 2.46/2.69      (![X19 : $i]:
% 2.46/2.69         (((k5_relat_1 @ X19 @ (k6_relat_1 @ (k2_relat_1 @ X19))) = (X19))
% 2.46/2.69          | ~ (v1_relat_1 @ X19))),
% 2.46/2.69      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.46/2.69  thf(t55_relat_1, axiom,
% 2.46/2.69    (![A:$i]:
% 2.46/2.69     ( ( v1_relat_1 @ A ) =>
% 2.46/2.69       ( ![B:$i]:
% 2.46/2.69         ( ( v1_relat_1 @ B ) =>
% 2.46/2.69           ( ![C:$i]:
% 2.46/2.69             ( ( v1_relat_1 @ C ) =>
% 2.46/2.69               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.46/2.69                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.46/2.69  thf('9', plain,
% 2.46/2.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X11)
% 2.46/2.69          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 2.46/2.69              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 2.46/2.69          | ~ (v1_relat_1 @ X13)
% 2.46/2.69          | ~ (v1_relat_1 @ X12))),
% 2.46/2.69      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.46/2.69  thf('10', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k5_relat_1 @ X0 @ X1)
% 2.46/2.69            = (k5_relat_1 @ X0 @ 
% 2.46/2.69               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 2.46/2.69          | ~ (v1_relat_1 @ X0)
% 2.46/2.69          | ~ (v1_relat_1 @ X0)
% 2.46/2.69          | ~ (v1_relat_1 @ X1)
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 2.46/2.69      inference('sup+', [status(thm)], ['8', '9'])).
% 2.46/2.69  thf('11', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('12', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k5_relat_1 @ X0 @ X1)
% 2.46/2.69            = (k5_relat_1 @ X0 @ 
% 2.46/2.69               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 2.46/2.69          | ~ (v1_relat_1 @ X0)
% 2.46/2.69          | ~ (v1_relat_1 @ X0)
% 2.46/2.69          | ~ (v1_relat_1 @ X1))),
% 2.46/2.69      inference('demod', [status(thm)], ['10', '11'])).
% 2.46/2.69  thf('13', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X1)
% 2.46/2.69          | ~ (v1_relat_1 @ X0)
% 2.46/2.69          | ((k5_relat_1 @ X0 @ X1)
% 2.46/2.69              = (k5_relat_1 @ X0 @ 
% 2.46/2.69                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))))),
% 2.46/2.69      inference('simplify', [status(thm)], ['12'])).
% 2.46/2.69  thf('14', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.46/2.69            = (k7_relat_1 @ 
% 2.46/2.69               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ 
% 2.46/2.69                X1) @ 
% 2.46/2.69               X0))
% 2.46/2.69          | ~ (v1_relat_1 @ 
% 2.46/2.69               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ 
% 2.46/2.69                X1))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['7', '13'])).
% 2.46/2.69  thf(t71_relat_1, axiom,
% 2.46/2.69    (![A:$i]:
% 2.46/2.69     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.46/2.69       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.46/2.69  thf('15', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 2.46/2.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.46/2.69  thf('16', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 2.46/2.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.46/2.69  thf('17', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('18', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.46/2.69            = (k7_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.46/2.69          | ~ (v1_relat_1 @ X1))),
% 2.46/2.69      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 2.46/2.69  thf('19', plain,
% 2.46/2.69      (![X22 : $i, X23 : $i]:
% 2.46/2.69         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 2.46/2.69          | ~ (v1_relat_1 @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.46/2.69  thf('20', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 2.46/2.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.46/2.69  thf(t78_relat_1, axiom,
% 2.46/2.69    (![A:$i]:
% 2.46/2.69     ( ( v1_relat_1 @ A ) =>
% 2.46/2.69       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 2.46/2.69  thf('21', plain,
% 2.46/2.69      (![X16 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 2.46/2.69          | ~ (v1_relat_1 @ X16))),
% 2.46/2.69      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.46/2.69  thf('22', plain,
% 2.46/2.69      (![X0 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.46/2.69            = (k6_relat_1 @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['20', '21'])).
% 2.46/2.69  thf('23', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('24', plain,
% 2.46/2.69      (![X0 : $i]:
% 2.46/2.69         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.46/2.69           = (k6_relat_1 @ X0))),
% 2.46/2.69      inference('demod', [status(thm)], ['22', '23'])).
% 2.46/2.69  thf('25', plain,
% 2.46/2.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X11)
% 2.46/2.69          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 2.46/2.69              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 2.46/2.69          | ~ (v1_relat_1 @ X13)
% 2.46/2.69          | ~ (v1_relat_1 @ X12))),
% 2.46/2.69      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.46/2.69  thf('26', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.46/2.69            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.46/2.69               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ X1)
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['24', '25'])).
% 2.46/2.69  thf('27', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('28', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('29', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.46/2.69            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.46/2.69               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.46/2.69          | ~ (v1_relat_1 @ X1))),
% 2.46/2.69      inference('demod', [status(thm)], ['26', '27', '28'])).
% 2.46/2.69  thf('30', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.46/2.69            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k7_relat_1 @ X1 @ X0)))
% 2.46/2.69          | ~ (v1_relat_1 @ X1)
% 2.46/2.69          | ~ (v1_relat_1 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['19', '29'])).
% 2.46/2.69  thf('31', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X1)
% 2.46/2.69          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.46/2.69              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k7_relat_1 @ X1 @ X0))))),
% 2.46/2.69      inference('simplify', [status(thm)], ['30'])).
% 2.46/2.69  thf(dt_k5_relat_1, axiom,
% 2.46/2.69    (![A:$i,B:$i]:
% 2.46/2.69     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 2.46/2.69       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 2.46/2.69  thf('32', plain,
% 2.46/2.69      (![X8 : $i, X9 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X8)
% 2.46/2.69          | ~ (v1_relat_1 @ X9)
% 2.46/2.69          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.46/2.69  thf('33', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ X0)
% 2.46/2.69          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['31', '32'])).
% 2.46/2.69  thf('34', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('35', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ X0)
% 2.46/2.69          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 2.46/2.69      inference('demod', [status(thm)], ['33', '34'])).
% 2.46/2.69  thf('36', plain,
% 2.46/2.69      (![X22 : $i, X23 : $i]:
% 2.46/2.69         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 2.46/2.69          | ~ (v1_relat_1 @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.46/2.69  thf('37', plain,
% 2.46/2.69      (![X8 : $i, X9 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X8)
% 2.46/2.69          | ~ (v1_relat_1 @ X9)
% 2.46/2.69          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.46/2.69  thf('38', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ X1)
% 2.46/2.69          | ~ (v1_relat_1 @ X1)
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['36', '37'])).
% 2.46/2.69  thf('39', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('40', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ X1)
% 2.46/2.69          | ~ (v1_relat_1 @ X1))),
% 2.46/2.69      inference('demod', [status(thm)], ['38', '39'])).
% 2.46/2.69  thf('41', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.46/2.69      inference('simplify', [status(thm)], ['40'])).
% 2.46/2.69  thf('42', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X0)
% 2.46/2.69          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.46/2.69      inference('clc', [status(thm)], ['35', '41'])).
% 2.46/2.69  thf('43', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X1)
% 2.46/2.69          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.46/2.69              = (k7_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)))),
% 2.46/2.69      inference('clc', [status(thm)], ['18', '42'])).
% 2.46/2.69  thf('44', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.46/2.69            = (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ X1)
% 2.46/2.69          | ~ (v1_relat_1 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['6', '43'])).
% 2.46/2.69  thf('45', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X1)
% 2.46/2.69          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.46/2.69              = (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)))),
% 2.46/2.69      inference('simplify', [status(thm)], ['44'])).
% 2.46/2.69  thf('46', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 2.46/2.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.46/2.69  thf(t90_relat_1, axiom,
% 2.46/2.69    (![A:$i,B:$i]:
% 2.46/2.69     ( ( v1_relat_1 @ B ) =>
% 2.46/2.69       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 2.46/2.69         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.46/2.69  thf('47', plain,
% 2.46/2.69      (![X20 : $i, X21 : $i]:
% 2.46/2.69         (((k1_relat_1 @ (k7_relat_1 @ X20 @ X21))
% 2.46/2.69            = (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21))
% 2.46/2.69          | ~ (v1_relat_1 @ X20))),
% 2.46/2.69      inference('cnf', [status(esa)], [t90_relat_1])).
% 2.46/2.69  thf('48', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.46/2.69            = (k3_xboole_0 @ X0 @ X1))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['46', '47'])).
% 2.46/2.69  thf('49', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('50', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.46/2.69           = (k3_xboole_0 @ X0 @ X1))),
% 2.46/2.69      inference('demod', [status(thm)], ['48', '49'])).
% 2.46/2.69  thf('51', plain,
% 2.46/2.69      (![X20 : $i, X21 : $i]:
% 2.46/2.69         (((k1_relat_1 @ (k7_relat_1 @ X20 @ X21))
% 2.46/2.69            = (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21))
% 2.46/2.69          | ~ (v1_relat_1 @ X20))),
% 2.46/2.69      inference('cnf', [status(esa)], [t90_relat_1])).
% 2.46/2.69  thf('52', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         (((k1_relat_1 @ 
% 2.46/2.69            (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))
% 2.46/2.69            = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 2.46/2.69          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['50', '51'])).
% 2.46/2.69  thf('53', plain,
% 2.46/2.69      (![X22 : $i, X23 : $i]:
% 2.46/2.69         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 2.46/2.69          | ~ (v1_relat_1 @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.46/2.69  thf('54', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.46/2.69      inference('simplify', [status(thm)], ['40'])).
% 2.46/2.69  thf('55', plain,
% 2.46/2.69      (![X0 : $i]:
% 2.46/2.69         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.46/2.69           = (k6_relat_1 @ X0))),
% 2.46/2.69      inference('demod', [status(thm)], ['22', '23'])).
% 2.46/2.69  thf('56', plain,
% 2.46/2.69      (![X22 : $i, X23 : $i]:
% 2.46/2.69         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 2.46/2.69          | ~ (v1_relat_1 @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.46/2.69  thf('57', plain,
% 2.46/2.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X11)
% 2.46/2.69          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 2.46/2.69              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 2.46/2.69          | ~ (v1_relat_1 @ X13)
% 2.46/2.69          | ~ (v1_relat_1 @ X12))),
% 2.46/2.69      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.46/2.69  thf('58', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.46/2.69            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 2.46/2.69          | ~ (v1_relat_1 @ X1)
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ X2)
% 2.46/2.69          | ~ (v1_relat_1 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['56', '57'])).
% 2.46/2.69  thf('59', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('60', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.46/2.69            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 2.46/2.69          | ~ (v1_relat_1 @ X1)
% 2.46/2.69          | ~ (v1_relat_1 @ X2)
% 2.46/2.69          | ~ (v1_relat_1 @ X1))),
% 2.46/2.69      inference('demod', [status(thm)], ['58', '59'])).
% 2.46/2.69  thf('61', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X2)
% 2.46/2.69          | ~ (v1_relat_1 @ X1)
% 2.46/2.69          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.46/2.69              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 2.46/2.69      inference('simplify', [status(thm)], ['60'])).
% 2.46/2.69  thf('62', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 2.46/2.69            (k6_relat_1 @ X0))
% 2.46/2.69            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['55', '61'])).
% 2.46/2.69  thf('63', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('64', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('65', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 2.46/2.69           (k6_relat_1 @ X0))
% 2.46/2.69           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 2.46/2.69      inference('demod', [status(thm)], ['62', '63', '64'])).
% 2.46/2.69  thf('66', plain,
% 2.46/2.69      (![X8 : $i, X9 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X8)
% 2.46/2.69          | ~ (v1_relat_1 @ X9)
% 2.46/2.69          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.46/2.69  thf('67', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['65', '66'])).
% 2.46/2.69  thf('68', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('69', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.46/2.69          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 2.46/2.69      inference('demod', [status(thm)], ['67', '68'])).
% 2.46/2.69  thf('70', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.46/2.69          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 2.46/2.69      inference('sup-', [status(thm)], ['54', '69'])).
% 2.46/2.69  thf('71', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('72', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.46/2.69      inference('demod', [status(thm)], ['70', '71'])).
% 2.46/2.69  thf('73', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['53', '72'])).
% 2.46/2.69  thf('74', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('75', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.46/2.69      inference('demod', [status(thm)], ['73', '74'])).
% 2.46/2.69  thf('76', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         ((k1_relat_1 @ 
% 2.46/2.69           (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))
% 2.46/2.69           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 2.46/2.69      inference('demod', [status(thm)], ['52', '75'])).
% 2.46/2.69  thf('77', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.46/2.69            = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['45', '76'])).
% 2.46/2.69  thf(commutativity_k2_tarski, axiom,
% 2.46/2.69    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.46/2.69  thf('78', plain,
% 2.46/2.69      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 2.46/2.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.46/2.69  thf(t12_setfam_1, axiom,
% 2.46/2.69    (![A:$i,B:$i]:
% 2.46/2.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.46/2.69  thf('79', plain,
% 2.46/2.69      (![X6 : $i, X7 : $i]:
% 2.46/2.69         ((k1_setfam_1 @ (k2_tarski @ X6 @ X7)) = (k3_xboole_0 @ X6 @ X7))),
% 2.46/2.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.46/2.69  thf('80', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['78', '79'])).
% 2.46/2.69  thf('81', plain,
% 2.46/2.69      (![X6 : $i, X7 : $i]:
% 2.46/2.69         ((k1_setfam_1 @ (k2_tarski @ X6 @ X7)) = (k3_xboole_0 @ X6 @ X7))),
% 2.46/2.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.46/2.69  thf('82', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['80', '81'])).
% 2.46/2.69  thf('83', plain,
% 2.46/2.69      (![X22 : $i, X23 : $i]:
% 2.46/2.69         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 2.46/2.69          | ~ (v1_relat_1 @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.46/2.69  thf(t17_xboole_1, axiom,
% 2.46/2.69    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.46/2.69  thf('84', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 2.46/2.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.46/2.69  thf('85', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 2.46/2.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.46/2.69  thf(t79_relat_1, axiom,
% 2.46/2.69    (![A:$i,B:$i]:
% 2.46/2.69     ( ( v1_relat_1 @ B ) =>
% 2.46/2.69       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.46/2.69         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 2.46/2.69  thf('86', plain,
% 2.46/2.69      (![X17 : $i, X18 : $i]:
% 2.46/2.69         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 2.46/2.69          | ((k5_relat_1 @ X17 @ (k6_relat_1 @ X18)) = (X17))
% 2.46/2.69          | ~ (v1_relat_1 @ X17))),
% 2.46/2.69      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.46/2.69  thf('87', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (~ (r1_tarski @ X0 @ X1)
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.46/2.69          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.46/2.69              = (k6_relat_1 @ X0)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['85', '86'])).
% 2.46/2.69  thf('88', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('89', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (~ (r1_tarski @ X0 @ X1)
% 2.46/2.69          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.46/2.69              = (k6_relat_1 @ X0)))),
% 2.46/2.69      inference('demod', [status(thm)], ['87', '88'])).
% 2.46/2.69  thf('90', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.46/2.69           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['84', '89'])).
% 2.46/2.69  thf('91', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.46/2.69            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['83', '90'])).
% 2.46/2.69  thf('92', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('93', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.46/2.69           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.46/2.69      inference('demod', [status(thm)], ['91', '92'])).
% 2.46/2.69  thf('94', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.46/2.69           = (k3_xboole_0 @ X0 @ X1))),
% 2.46/2.69      inference('demod', [status(thm)], ['48', '49'])).
% 2.46/2.69  thf('95', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.46/2.69           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['93', '94'])).
% 2.46/2.69  thf('96', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 2.46/2.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.46/2.69  thf('97', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k3_xboole_0 @ X1 @ X0)
% 2.46/2.69           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.46/2.69      inference('demod', [status(thm)], ['95', '96'])).
% 2.46/2.69  thf('98', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k3_xboole_0 @ X0 @ X1)
% 2.46/2.69           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['82', '97'])).
% 2.46/2.69  thf('99', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k3_xboole_0 @ X0 @ X1)
% 2.46/2.69           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['82', '97'])).
% 2.46/2.69  thf('100', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)
% 2.46/2.69           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['98', '99'])).
% 2.46/2.69  thf('101', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['80', '81'])).
% 2.46/2.69  thf('102', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k3_xboole_0 @ X0 @ X1)
% 2.46/2.69           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['82', '97'])).
% 2.46/2.69  thf('103', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k3_xboole_0 @ X1 @ X0)
% 2.46/2.69           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.46/2.69      inference('demod', [status(thm)], ['100', '101', '102'])).
% 2.46/2.69  thf('104', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['80', '81'])).
% 2.46/2.69  thf('105', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 2.46/2.69           = (k3_xboole_0 @ X1 @ X0))),
% 2.46/2.69      inference('sup+', [status(thm)], ['103', '104'])).
% 2.46/2.69  thf('106', plain,
% 2.46/2.69      (![X22 : $i, X23 : $i]:
% 2.46/2.69         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 2.46/2.69          | ~ (v1_relat_1 @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.46/2.69  thf('107', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.46/2.69           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['84', '89'])).
% 2.46/2.69  thf('108', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.46/2.69           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['84', '89'])).
% 2.46/2.69  thf('109', plain,
% 2.46/2.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X11)
% 2.46/2.69          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 2.46/2.69              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 2.46/2.69          | ~ (v1_relat_1 @ X13)
% 2.46/2.69          | ~ (v1_relat_1 @ X12))),
% 2.46/2.69      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.46/2.69  thf('110', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 2.46/2.69            = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.46/2.69               (k5_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.46/2.69          | ~ (v1_relat_1 @ X2)
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['108', '109'])).
% 2.46/2.69  thf('111', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('112', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('113', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 2.46/2.69            = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.46/2.69               (k5_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 2.46/2.69          | ~ (v1_relat_1 @ X2))),
% 2.46/2.69      inference('demod', [status(thm)], ['110', '111', '112'])).
% 2.46/2.69  thf('114', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         (((k5_relat_1 @ 
% 2.46/2.69            (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)) @ 
% 2.46/2.69            (k6_relat_1 @ X1))
% 2.46/2.69            = (k5_relat_1 @ 
% 2.46/2.69               (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)) @ 
% 2.46/2.69               (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['107', '113'])).
% 2.46/2.69  thf('115', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.46/2.69           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['84', '89'])).
% 2.46/2.69  thf('116', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('117', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         ((k5_relat_1 @ 
% 2.46/2.69           (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)) @ 
% 2.46/2.69           (k6_relat_1 @ X1))
% 2.46/2.69           = (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 2.46/2.69      inference('demod', [status(thm)], ['114', '115', '116'])).
% 2.46/2.69  thf('118', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         (((k7_relat_1 @ (k6_relat_1 @ X2) @ 
% 2.46/2.69            (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 2.46/2.69            = (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['106', '117'])).
% 2.46/2.69  thf('119', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('120', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k6_relat_1 @ X2) @ 
% 2.46/2.69           (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 2.46/2.69           = (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 2.46/2.69      inference('demod', [status(thm)], ['118', '119'])).
% 2.46/2.69  thf('121', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.46/2.69           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 2.46/2.69           = (k6_relat_1 @ 
% 2.46/2.69              (k3_xboole_0 @ 
% 2.46/2.69               (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.46/2.69               X2)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['105', '120'])).
% 2.46/2.69  thf('122', plain,
% 2.46/2.69      (![X22 : $i, X23 : $i]:
% 2.46/2.69         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 2.46/2.69          | ~ (v1_relat_1 @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.46/2.69  thf('123', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['80', '81'])).
% 2.46/2.69  thf('124', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['80', '81'])).
% 2.46/2.69  thf('125', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 2.46/2.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.46/2.69  thf('126', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.46/2.69      inference('sup+', [status(thm)], ['124', '125'])).
% 2.46/2.69  thf('127', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (~ (r1_tarski @ X0 @ X1)
% 2.46/2.69          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.46/2.69              = (k6_relat_1 @ X0)))),
% 2.46/2.69      inference('demod', [status(thm)], ['87', '88'])).
% 2.46/2.69  thf('128', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.46/2.69           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['126', '127'])).
% 2.46/2.69  thf('129', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.46/2.69           (k6_relat_1 @ X1)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['123', '128'])).
% 2.46/2.69  thf('130', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.46/2.69            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['122', '129'])).
% 2.46/2.69  thf('131', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('132', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.46/2.69           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.46/2.69      inference('demod', [status(thm)], ['130', '131'])).
% 2.46/2.69  thf('133', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k3_xboole_0 @ X1 @ X0)
% 2.46/2.69           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.46/2.69      inference('demod', [status(thm)], ['100', '101', '102'])).
% 2.46/2.69  thf('134', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         ((k6_relat_1 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 2.46/2.69           = (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)))),
% 2.46/2.69      inference('demod', [status(thm)], ['121', '132', '133'])).
% 2.46/2.69  thf('135', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 2.46/2.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.46/2.69  thf('136', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         ((k1_relat_1 @ 
% 2.46/2.69           (k6_relat_1 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))
% 2.46/2.69           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 2.46/2.69      inference('sup+', [status(thm)], ['134', '135'])).
% 2.46/2.69  thf('137', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 2.46/2.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.46/2.69  thf('138', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.46/2.69           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 2.46/2.69      inference('demod', [status(thm)], ['136', '137'])).
% 2.46/2.69  thf('139', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k3_xboole_0 @ X1 @ X0)
% 2.46/2.69           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.46/2.69      inference('demod', [status(thm)], ['95', '96'])).
% 2.46/2.69  thf('140', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('141', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.46/2.69           = (k3_xboole_0 @ X1 @ X0))),
% 2.46/2.69      inference('demod', [status(thm)], ['77', '138', '139', '140'])).
% 2.46/2.69  thf('142', plain,
% 2.46/2.69      (![X16 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 2.46/2.69          | ~ (v1_relat_1 @ X16))),
% 2.46/2.69      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.46/2.69  thf('143', plain,
% 2.46/2.69      (![X22 : $i, X23 : $i]:
% 2.46/2.69         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 2.46/2.69          | ~ (v1_relat_1 @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.46/2.69  thf('144', plain,
% 2.46/2.69      (![X0 : $i]:
% 2.46/2.69         (((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0))
% 2.46/2.69          | ~ (v1_relat_1 @ X0)
% 2.46/2.69          | ~ (v1_relat_1 @ X0))),
% 2.46/2.69      inference('sup+', [status(thm)], ['142', '143'])).
% 2.46/2.69  thf('145', plain,
% 2.46/2.69      (![X0 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 2.46/2.69      inference('simplify', [status(thm)], ['144'])).
% 2.46/2.69  thf('146', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k7_relat_1 @ 
% 2.46/2.69            (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ 
% 2.46/2.69            (k3_xboole_0 @ X1 @ X0))
% 2.46/2.69            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.46/2.69          | ~ (v1_relat_1 @ 
% 2.46/2.69               (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 2.46/2.69      inference('sup+', [status(thm)], ['141', '145'])).
% 2.46/2.69  thf('147', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.46/2.69      inference('demod', [status(thm)], ['70', '71'])).
% 2.46/2.69  thf('148', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ 
% 2.46/2.69           (k3_xboole_0 @ X1 @ X0))
% 2.46/2.69           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 2.46/2.69      inference('demod', [status(thm)], ['146', '147'])).
% 2.46/2.69  thf('149', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.46/2.69            (k3_xboole_0 @ X0 @ X1))
% 2.46/2.69            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['5', '148'])).
% 2.46/2.69  thf('150', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['80', '81'])).
% 2.46/2.69  thf('151', plain,
% 2.46/2.69      (![X22 : $i, X23 : $i]:
% 2.46/2.69         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 2.46/2.69          | ~ (v1_relat_1 @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.46/2.69  thf('152', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.46/2.69           = (k3_xboole_0 @ X0 @ X1))),
% 2.46/2.69      inference('demod', [status(thm)], ['48', '49'])).
% 2.46/2.69  thf('153', plain,
% 2.46/2.69      (![X16 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 2.46/2.69          | ~ (v1_relat_1 @ X16))),
% 2.46/2.69      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.46/2.69  thf('154', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.46/2.69            (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.46/2.69            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['152', '153'])).
% 2.46/2.69  thf('155', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.46/2.69      inference('demod', [status(thm)], ['73', '74'])).
% 2.46/2.69  thf('156', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.46/2.69           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.46/2.69           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.46/2.69      inference('demod', [status(thm)], ['154', '155'])).
% 2.46/2.69  thf('157', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.46/2.69            (k3_xboole_0 @ X1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['151', '156'])).
% 2.46/2.69  thf('158', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.46/2.69      inference('demod', [status(thm)], ['73', '74'])).
% 2.46/2.69  thf('159', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.46/2.69           (k3_xboole_0 @ X1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.46/2.69      inference('demod', [status(thm)], ['157', '158'])).
% 2.46/2.69  thf('160', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 2.46/2.69           (k3_xboole_0 @ X1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['150', '159'])).
% 2.46/2.69  thf('161', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('162', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.46/2.69           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.46/2.69      inference('demod', [status(thm)], ['149', '160', '161'])).
% 2.46/2.69  thf('163', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ X2)
% 2.46/2.69          | ~ (v1_relat_1 @ X1)
% 2.46/2.69          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.46/2.69              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 2.46/2.69      inference('simplify', [status(thm)], ['60'])).
% 2.46/2.69  thf('164', plain,
% 2.46/2.69      (![X16 : $i]:
% 2.46/2.69         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 2.46/2.69          | ~ (v1_relat_1 @ X16))),
% 2.46/2.69      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.46/2.69  thf('165', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (((k5_relat_1 @ 
% 2.46/2.69            (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0)
% 2.46/2.69            = (k5_relat_1 @ X1 @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ X1)
% 2.46/2.69          | ~ (v1_relat_1 @ X0)
% 2.46/2.69          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 2.46/2.69      inference('sup+', [status(thm)], ['163', '164'])).
% 2.46/2.69  thf('166', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.46/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.46/2.69          | ((k5_relat_1 @ 
% 2.46/2.69              (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.46/2.69               (k1_relat_1 @ 
% 2.46/2.69                (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))) @ 
% 2.46/2.69              (k6_relat_1 @ X1))
% 2.46/2.69              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 2.46/2.69      inference('sup-', [status(thm)], ['162', '165'])).
% 2.46/2.69  thf('167', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.46/2.69      inference('demod', [status(thm)], ['73', '74'])).
% 2.46/2.69  thf('168', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('169', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.46/2.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.46/2.69  thf('170', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.46/2.69           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.46/2.69      inference('demod', [status(thm)], ['149', '160', '161'])).
% 2.46/2.69  thf('171', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.46/2.69           = (k3_xboole_0 @ X1 @ X0))),
% 2.46/2.69      inference('demod', [status(thm)], ['77', '138', '139', '140'])).
% 2.46/2.69  thf('172', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.46/2.69           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.46/2.69      inference('demod', [status(thm)], ['149', '160', '161'])).
% 2.46/2.69  thf('173', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.46/2.69           = (k3_xboole_0 @ X1 @ X0))),
% 2.46/2.69      inference('demod', [status(thm)], ['171', '172'])).
% 2.46/2.69  thf('174', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.46/2.69           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.46/2.69      inference('demod', [status(thm)], ['130', '131'])).
% 2.46/2.69  thf('175', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.46/2.69           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.46/2.69      inference('demod', [status(thm)], ['149', '160', '161'])).
% 2.46/2.69  thf('176', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.46/2.69           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.46/2.69      inference('demod', [status(thm)], ['130', '131'])).
% 2.46/2.69  thf('177', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.46/2.69           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.46/2.69      inference('demod', [status(thm)], ['149', '160', '161'])).
% 2.46/2.69  thf('178', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 2.46/2.69           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.46/2.69      inference('demod', [status(thm)],
% 2.46/2.69                ['166', '167', '168', '169', '170', '173', '174', '175', 
% 2.46/2.69                 '176', '177'])).
% 2.46/2.69  thf('179', plain,
% 2.46/2.69      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.46/2.69         != (k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A))),
% 2.46/2.69      inference('demod', [status(thm)], ['4', '178'])).
% 2.46/2.69  thf('180', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['80', '81'])).
% 2.46/2.69  thf('181', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 2.46/2.69           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.46/2.69      inference('demod', [status(thm)],
% 2.46/2.69                ['166', '167', '168', '169', '170', '173', '174', '175', 
% 2.46/2.69                 '176', '177'])).
% 2.46/2.69  thf('182', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 2.46/2.69           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.46/2.69      inference('sup+', [status(thm)], ['180', '181'])).
% 2.46/2.69  thf('183', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 2.46/2.69           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.46/2.69      inference('demod', [status(thm)],
% 2.46/2.69                ['166', '167', '168', '169', '170', '173', '174', '175', 
% 2.46/2.69                 '176', '177'])).
% 2.46/2.69  thf('184', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.46/2.69           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['182', '183'])).
% 2.46/2.69  thf('185', plain,
% 2.46/2.69      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.46/2.69         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 2.46/2.69      inference('demod', [status(thm)], ['179', '184'])).
% 2.46/2.69  thf('186', plain, ($false), inference('simplify', [status(thm)], ['185'])).
% 2.46/2.69  
% 2.46/2.69  % SZS output end Refutation
% 2.46/2.69  
% 2.46/2.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
