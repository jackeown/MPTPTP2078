%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DyjSwEURLl

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:01 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  207 (10815 expanded)
%              Number of leaves         :   23 (3633 expanded)
%              Depth                    :   27
%              Number of atoms          : 1983 (97232 expanded)
%              Number of equality atoms :  144 (7474 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('8',plain,(
    ! [X21: $i] :
      ( ( ( k5_relat_1 @ X21 @ ( k6_relat_1 @ ( k2_relat_1 @ X21 ) ) )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k5_relat_1 @ X14 @ ( k5_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

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
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('17',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('20',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('21',plain,(
    ! [X18: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k5_relat_1 @ X14 @ ( k5_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

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
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

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
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('57',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k5_relat_1 @ X14 @ ( k5_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

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
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('64',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

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
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

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
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('81',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('82',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['79','86'])).

thf('88',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','93'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','93'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('105',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k5_relat_1 @ X14 @ ( k5_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('108',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['103','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('112',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['102','113'])).

thf('115',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['101','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('119',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('121',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['119','124'])).

thf('126',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['118','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['117','128','129'])).

thf('131',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('136',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','134','135','136'])).

thf('138',plain,(
    ! [X18: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('139',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['137','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('147',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('149',plain,(
    ! [X18: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['147','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['146','155'])).

thf('157',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['145','156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('160',plain,(
    ! [X18: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['158','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('164',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('165',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['145','156','157'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','134','135','136'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['145','156','157'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['118','127'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['145','156','157'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['118','127'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['145','156','157'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['162','163','164','165','166','169','170','171','172','173'])).

thf('175',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['4','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['162','163','164','165','166','169','170','171','172','173'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['162','163','164','165','166','169','170','171','172','173'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['175','180'])).

thf('182',plain,(
    $false ),
    inference(simplify,[status(thm)],['181'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DyjSwEURLl
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:56:11 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.11/2.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.11/2.31  % Solved by: fo/fo7.sh
% 2.11/2.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.11/2.31  % done 2108 iterations in 1.848s
% 2.11/2.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.11/2.31  % SZS output start Refutation
% 2.11/2.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.11/2.31  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.11/2.31  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.11/2.31  thf(sk_A_type, type, sk_A: $i).
% 2.11/2.31  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.11/2.31  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.11/2.31  thf(sk_B_type, type, sk_B: $i).
% 2.11/2.31  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.11/2.31  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.11/2.31  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.11/2.31  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.11/2.31  thf(t94_relat_1, axiom,
% 2.11/2.31    (![A:$i,B:$i]:
% 2.11/2.31     ( ( v1_relat_1 @ B ) =>
% 2.11/2.31       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.11/2.31  thf('0', plain,
% 2.11/2.31      (![X24 : $i, X25 : $i]:
% 2.11/2.31         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 2.11/2.31          | ~ (v1_relat_1 @ X25))),
% 2.11/2.31      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.11/2.31  thf(t43_funct_1, conjecture,
% 2.11/2.31    (![A:$i,B:$i]:
% 2.11/2.31     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.11/2.31       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.11/2.31  thf(zf_stmt_0, negated_conjecture,
% 2.11/2.31    (~( ![A:$i,B:$i]:
% 2.11/2.31        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.11/2.31          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 2.11/2.31    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 2.11/2.31  thf('1', plain,
% 2.11/2.31      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 2.11/2.31         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.11/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.31  thf('2', plain,
% 2.11/2.31      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.11/2.31          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 2.11/2.31        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 2.11/2.31      inference('sup-', [status(thm)], ['0', '1'])).
% 2.11/2.31  thf(fc3_funct_1, axiom,
% 2.11/2.31    (![A:$i]:
% 2.11/2.31     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.11/2.31       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.11/2.31  thf('3', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('4', plain,
% 2.11/2.31      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.11/2.31         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.11/2.31      inference('demod', [status(thm)], ['2', '3'])).
% 2.11/2.31  thf('5', plain,
% 2.11/2.31      (![X24 : $i, X25 : $i]:
% 2.11/2.31         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 2.11/2.31          | ~ (v1_relat_1 @ X25))),
% 2.11/2.31      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.11/2.31  thf('6', plain,
% 2.11/2.31      (![X24 : $i, X25 : $i]:
% 2.11/2.31         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 2.11/2.31          | ~ (v1_relat_1 @ X25))),
% 2.11/2.31      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.11/2.31  thf('7', plain,
% 2.11/2.31      (![X24 : $i, X25 : $i]:
% 2.11/2.31         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 2.11/2.31          | ~ (v1_relat_1 @ X25))),
% 2.11/2.31      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.11/2.31  thf(t80_relat_1, axiom,
% 2.11/2.31    (![A:$i]:
% 2.11/2.31     ( ( v1_relat_1 @ A ) =>
% 2.11/2.31       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.11/2.31  thf('8', plain,
% 2.11/2.31      (![X21 : $i]:
% 2.11/2.31         (((k5_relat_1 @ X21 @ (k6_relat_1 @ (k2_relat_1 @ X21))) = (X21))
% 2.11/2.31          | ~ (v1_relat_1 @ X21))),
% 2.11/2.31      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.11/2.31  thf(t55_relat_1, axiom,
% 2.11/2.31    (![A:$i]:
% 2.11/2.31     ( ( v1_relat_1 @ A ) =>
% 2.11/2.31       ( ![B:$i]:
% 2.11/2.31         ( ( v1_relat_1 @ B ) =>
% 2.11/2.31           ( ![C:$i]:
% 2.11/2.31             ( ( v1_relat_1 @ C ) =>
% 2.11/2.31               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.11/2.31                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.11/2.31  thf('9', plain,
% 2.11/2.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X13)
% 2.11/2.31          | ((k5_relat_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 2.11/2.31              = (k5_relat_1 @ X14 @ (k5_relat_1 @ X13 @ X15)))
% 2.11/2.31          | ~ (v1_relat_1 @ X15)
% 2.11/2.31          | ~ (v1_relat_1 @ X14))),
% 2.11/2.31      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.11/2.31  thf('10', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k5_relat_1 @ X0 @ X1)
% 2.11/2.31            = (k5_relat_1 @ X0 @ 
% 2.11/2.31               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 2.11/2.31          | ~ (v1_relat_1 @ X0)
% 2.11/2.31          | ~ (v1_relat_1 @ X0)
% 2.11/2.31          | ~ (v1_relat_1 @ X1)
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 2.11/2.31      inference('sup+', [status(thm)], ['8', '9'])).
% 2.11/2.31  thf('11', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('12', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k5_relat_1 @ X0 @ X1)
% 2.11/2.31            = (k5_relat_1 @ X0 @ 
% 2.11/2.31               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 2.11/2.31          | ~ (v1_relat_1 @ X0)
% 2.11/2.31          | ~ (v1_relat_1 @ X0)
% 2.11/2.31          | ~ (v1_relat_1 @ X1))),
% 2.11/2.31      inference('demod', [status(thm)], ['10', '11'])).
% 2.11/2.31  thf('13', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X1)
% 2.11/2.31          | ~ (v1_relat_1 @ X0)
% 2.11/2.31          | ((k5_relat_1 @ X0 @ X1)
% 2.11/2.31              = (k5_relat_1 @ X0 @ 
% 2.11/2.31                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))))),
% 2.11/2.31      inference('simplify', [status(thm)], ['12'])).
% 2.11/2.31  thf('14', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.11/2.31            = (k7_relat_1 @ 
% 2.11/2.31               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ 
% 2.11/2.31                X1) @ 
% 2.11/2.31               X0))
% 2.11/2.31          | ~ (v1_relat_1 @ 
% 2.11/2.31               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ 
% 2.11/2.31                X1))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ X1))),
% 2.11/2.31      inference('sup+', [status(thm)], ['7', '13'])).
% 2.11/2.31  thf(t71_relat_1, axiom,
% 2.11/2.31    (![A:$i]:
% 2.11/2.31     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.11/2.31       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.11/2.31  thf('15', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 2.11/2.31      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.11/2.31  thf('16', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 2.11/2.31      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.11/2.31  thf('17', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('18', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.11/2.31            = (k7_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.11/2.31          | ~ (v1_relat_1 @ X1))),
% 2.11/2.31      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 2.11/2.31  thf('19', plain,
% 2.11/2.31      (![X24 : $i, X25 : $i]:
% 2.11/2.31         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 2.11/2.31          | ~ (v1_relat_1 @ X25))),
% 2.11/2.31      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.11/2.31  thf('20', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 2.11/2.31      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.11/2.31  thf(t78_relat_1, axiom,
% 2.11/2.31    (![A:$i]:
% 2.11/2.31     ( ( v1_relat_1 @ A ) =>
% 2.11/2.31       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 2.11/2.31  thf('21', plain,
% 2.11/2.31      (![X18 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X18)) @ X18) = (X18))
% 2.11/2.31          | ~ (v1_relat_1 @ X18))),
% 2.11/2.31      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.11/2.31  thf('22', plain,
% 2.11/2.31      (![X0 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.11/2.31            = (k6_relat_1 @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['20', '21'])).
% 2.11/2.31  thf('23', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('24', plain,
% 2.11/2.31      (![X0 : $i]:
% 2.11/2.31         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.11/2.31           = (k6_relat_1 @ X0))),
% 2.11/2.31      inference('demod', [status(thm)], ['22', '23'])).
% 2.11/2.31  thf('25', plain,
% 2.11/2.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X13)
% 2.11/2.31          | ((k5_relat_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 2.11/2.31              = (k5_relat_1 @ X14 @ (k5_relat_1 @ X13 @ X15)))
% 2.11/2.31          | ~ (v1_relat_1 @ X15)
% 2.11/2.31          | ~ (v1_relat_1 @ X14))),
% 2.11/2.31      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.11/2.31  thf('26', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.11/2.31            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.11/2.31               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ X1)
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['24', '25'])).
% 2.11/2.31  thf('27', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('28', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('29', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.11/2.31            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.11/2.31               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.11/2.31          | ~ (v1_relat_1 @ X1))),
% 2.11/2.31      inference('demod', [status(thm)], ['26', '27', '28'])).
% 2.11/2.31  thf('30', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.11/2.31            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k7_relat_1 @ X1 @ X0)))
% 2.11/2.31          | ~ (v1_relat_1 @ X1)
% 2.11/2.31          | ~ (v1_relat_1 @ X1))),
% 2.11/2.31      inference('sup+', [status(thm)], ['19', '29'])).
% 2.11/2.31  thf('31', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X1)
% 2.11/2.31          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.11/2.31              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k7_relat_1 @ X1 @ X0))))),
% 2.11/2.31      inference('simplify', [status(thm)], ['30'])).
% 2.11/2.31  thf(dt_k5_relat_1, axiom,
% 2.11/2.31    (![A:$i,B:$i]:
% 2.11/2.31     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 2.11/2.31       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 2.11/2.31  thf('32', plain,
% 2.11/2.31      (![X11 : $i, X12 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X11)
% 2.11/2.31          | ~ (v1_relat_1 @ X12)
% 2.11/2.31          | (v1_relat_1 @ (k5_relat_1 @ X11 @ X12)))),
% 2.11/2.31      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.11/2.31  thf('33', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ X0)
% 2.11/2.31          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['31', '32'])).
% 2.11/2.31  thf('34', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('35', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ X0)
% 2.11/2.31          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 2.11/2.31      inference('demod', [status(thm)], ['33', '34'])).
% 2.11/2.31  thf('36', plain,
% 2.11/2.31      (![X24 : $i, X25 : $i]:
% 2.11/2.31         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 2.11/2.31          | ~ (v1_relat_1 @ X25))),
% 2.11/2.31      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.11/2.31  thf('37', plain,
% 2.11/2.31      (![X11 : $i, X12 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X11)
% 2.11/2.31          | ~ (v1_relat_1 @ X12)
% 2.11/2.31          | (v1_relat_1 @ (k5_relat_1 @ X11 @ X12)))),
% 2.11/2.31      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.11/2.31  thf('38', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ X1)
% 2.11/2.31          | ~ (v1_relat_1 @ X1)
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['36', '37'])).
% 2.11/2.31  thf('39', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('40', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ X1)
% 2.11/2.31          | ~ (v1_relat_1 @ X1))),
% 2.11/2.31      inference('demod', [status(thm)], ['38', '39'])).
% 2.11/2.31  thf('41', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.11/2.31      inference('simplify', [status(thm)], ['40'])).
% 2.11/2.31  thf('42', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X0)
% 2.11/2.31          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.11/2.31      inference('clc', [status(thm)], ['35', '41'])).
% 2.11/2.31  thf('43', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X1)
% 2.11/2.31          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.11/2.31              = (k7_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)))),
% 2.11/2.31      inference('clc', [status(thm)], ['18', '42'])).
% 2.11/2.31  thf('44', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.11/2.31            = (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ X1)
% 2.11/2.31          | ~ (v1_relat_1 @ X1))),
% 2.11/2.31      inference('sup+', [status(thm)], ['6', '43'])).
% 2.11/2.31  thf('45', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X1)
% 2.11/2.31          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.11/2.31              = (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)))),
% 2.11/2.31      inference('simplify', [status(thm)], ['44'])).
% 2.11/2.31  thf('46', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 2.11/2.31      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.11/2.31  thf(t90_relat_1, axiom,
% 2.11/2.31    (![A:$i,B:$i]:
% 2.11/2.31     ( ( v1_relat_1 @ B ) =>
% 2.11/2.31       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 2.11/2.31         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.11/2.31  thf('47', plain,
% 2.11/2.31      (![X22 : $i, X23 : $i]:
% 2.11/2.31         (((k1_relat_1 @ (k7_relat_1 @ X22 @ X23))
% 2.11/2.31            = (k3_xboole_0 @ (k1_relat_1 @ X22) @ X23))
% 2.11/2.31          | ~ (v1_relat_1 @ X22))),
% 2.11/2.31      inference('cnf', [status(esa)], [t90_relat_1])).
% 2.11/2.31  thf('48', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.11/2.31            = (k3_xboole_0 @ X0 @ X1))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['46', '47'])).
% 2.11/2.31  thf('49', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('50', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.11/2.31           = (k3_xboole_0 @ X0 @ X1))),
% 2.11/2.31      inference('demod', [status(thm)], ['48', '49'])).
% 2.11/2.31  thf('51', plain,
% 2.11/2.31      (![X22 : $i, X23 : $i]:
% 2.11/2.31         (((k1_relat_1 @ (k7_relat_1 @ X22 @ X23))
% 2.11/2.31            = (k3_xboole_0 @ (k1_relat_1 @ X22) @ X23))
% 2.11/2.31          | ~ (v1_relat_1 @ X22))),
% 2.11/2.31      inference('cnf', [status(esa)], [t90_relat_1])).
% 2.11/2.31  thf('52', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         (((k1_relat_1 @ 
% 2.11/2.31            (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))
% 2.11/2.31            = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 2.11/2.31          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['50', '51'])).
% 2.11/2.31  thf('53', plain,
% 2.11/2.31      (![X24 : $i, X25 : $i]:
% 2.11/2.31         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 2.11/2.31          | ~ (v1_relat_1 @ X25))),
% 2.11/2.31      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.11/2.31  thf('54', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.11/2.31      inference('simplify', [status(thm)], ['40'])).
% 2.11/2.31  thf('55', plain,
% 2.11/2.31      (![X0 : $i]:
% 2.11/2.31         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.11/2.31           = (k6_relat_1 @ X0))),
% 2.11/2.31      inference('demod', [status(thm)], ['22', '23'])).
% 2.11/2.31  thf('56', plain,
% 2.11/2.31      (![X24 : $i, X25 : $i]:
% 2.11/2.31         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 2.11/2.31          | ~ (v1_relat_1 @ X25))),
% 2.11/2.31      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.11/2.31  thf('57', plain,
% 2.11/2.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X13)
% 2.11/2.31          | ((k5_relat_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 2.11/2.31              = (k5_relat_1 @ X14 @ (k5_relat_1 @ X13 @ X15)))
% 2.11/2.31          | ~ (v1_relat_1 @ X15)
% 2.11/2.31          | ~ (v1_relat_1 @ X14))),
% 2.11/2.31      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.11/2.31  thf('58', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.11/2.31            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 2.11/2.31          | ~ (v1_relat_1 @ X1)
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ X2)
% 2.11/2.31          | ~ (v1_relat_1 @ X1))),
% 2.11/2.31      inference('sup+', [status(thm)], ['56', '57'])).
% 2.11/2.31  thf('59', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('60', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.11/2.31            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 2.11/2.31          | ~ (v1_relat_1 @ X1)
% 2.11/2.31          | ~ (v1_relat_1 @ X2)
% 2.11/2.31          | ~ (v1_relat_1 @ X1))),
% 2.11/2.31      inference('demod', [status(thm)], ['58', '59'])).
% 2.11/2.31  thf('61', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X2)
% 2.11/2.31          | ~ (v1_relat_1 @ X1)
% 2.11/2.31          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.11/2.31              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 2.11/2.31      inference('simplify', [status(thm)], ['60'])).
% 2.11/2.31  thf('62', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 2.11/2.31            (k6_relat_1 @ X0))
% 2.11/2.31            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['55', '61'])).
% 2.11/2.31  thf('63', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('64', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('65', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 2.11/2.31           (k6_relat_1 @ X0))
% 2.11/2.31           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 2.11/2.31      inference('demod', [status(thm)], ['62', '63', '64'])).
% 2.11/2.31  thf('66', plain,
% 2.11/2.31      (![X11 : $i, X12 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X11)
% 2.11/2.31          | ~ (v1_relat_1 @ X12)
% 2.11/2.31          | (v1_relat_1 @ (k5_relat_1 @ X11 @ X12)))),
% 2.11/2.31      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.11/2.31  thf('67', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['65', '66'])).
% 2.11/2.31  thf('68', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('69', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.11/2.31          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 2.11/2.31      inference('demod', [status(thm)], ['67', '68'])).
% 2.11/2.31  thf('70', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.11/2.31          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 2.11/2.31      inference('sup-', [status(thm)], ['54', '69'])).
% 2.11/2.31  thf('71', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('72', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.11/2.31      inference('demod', [status(thm)], ['70', '71'])).
% 2.11/2.31  thf('73', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['53', '72'])).
% 2.11/2.31  thf('74', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('75', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.11/2.31      inference('demod', [status(thm)], ['73', '74'])).
% 2.11/2.31  thf('76', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         ((k1_relat_1 @ 
% 2.11/2.31           (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))
% 2.11/2.31           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 2.11/2.31      inference('demod', [status(thm)], ['52', '75'])).
% 2.11/2.31  thf('77', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.11/2.31            = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['45', '76'])).
% 2.11/2.31  thf(commutativity_k3_xboole_0, axiom,
% 2.11/2.31    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.11/2.31  thf('78', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.11/2.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.11/2.31  thf('79', plain,
% 2.11/2.31      (![X24 : $i, X25 : $i]:
% 2.11/2.31         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 2.11/2.31          | ~ (v1_relat_1 @ X25))),
% 2.11/2.31      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.11/2.31  thf(t17_xboole_1, axiom,
% 2.11/2.31    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.11/2.31  thf('80', plain,
% 2.11/2.31      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 2.11/2.31      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.11/2.31  thf('81', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 2.11/2.31      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.11/2.31  thf(t79_relat_1, axiom,
% 2.11/2.31    (![A:$i,B:$i]:
% 2.11/2.31     ( ( v1_relat_1 @ B ) =>
% 2.11/2.31       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.11/2.31         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 2.11/2.31  thf('82', plain,
% 2.11/2.31      (![X19 : $i, X20 : $i]:
% 2.11/2.31         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 2.11/2.31          | ((k5_relat_1 @ X19 @ (k6_relat_1 @ X20)) = (X19))
% 2.11/2.31          | ~ (v1_relat_1 @ X19))),
% 2.11/2.31      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.11/2.31  thf('83', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (~ (r1_tarski @ X0 @ X1)
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.11/2.31          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.11/2.31              = (k6_relat_1 @ X0)))),
% 2.11/2.31      inference('sup-', [status(thm)], ['81', '82'])).
% 2.11/2.31  thf('84', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('85', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (~ (r1_tarski @ X0 @ X1)
% 2.11/2.31          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.11/2.31              = (k6_relat_1 @ X0)))),
% 2.11/2.31      inference('demod', [status(thm)], ['83', '84'])).
% 2.11/2.31  thf('86', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.11/2.31           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.11/2.31      inference('sup-', [status(thm)], ['80', '85'])).
% 2.11/2.31  thf('87', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.11/2.31            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['79', '86'])).
% 2.11/2.31  thf('88', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('89', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.11/2.31           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.11/2.31      inference('demod', [status(thm)], ['87', '88'])).
% 2.11/2.31  thf('90', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.11/2.31           = (k3_xboole_0 @ X0 @ X1))),
% 2.11/2.31      inference('demod', [status(thm)], ['48', '49'])).
% 2.11/2.31  thf('91', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.11/2.31           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['89', '90'])).
% 2.11/2.31  thf('92', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 2.11/2.31      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.11/2.31  thf('93', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k3_xboole_0 @ X1 @ X0)
% 2.11/2.31           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.11/2.31      inference('demod', [status(thm)], ['91', '92'])).
% 2.11/2.31  thf('94', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k3_xboole_0 @ X0 @ X1)
% 2.11/2.31           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['78', '93'])).
% 2.11/2.31  thf('95', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k3_xboole_0 @ X0 @ X1)
% 2.11/2.31           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['78', '93'])).
% 2.11/2.31  thf('96', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)
% 2.11/2.31           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['94', '95'])).
% 2.11/2.31  thf('97', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.11/2.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.11/2.31  thf('98', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k3_xboole_0 @ X0 @ X1)
% 2.11/2.31           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['78', '93'])).
% 2.11/2.31  thf('99', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k3_xboole_0 @ X1 @ X0)
% 2.11/2.31           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.11/2.31      inference('demod', [status(thm)], ['96', '97', '98'])).
% 2.11/2.31  thf('100', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.11/2.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.11/2.31  thf('101', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 2.11/2.31           = (k3_xboole_0 @ X1 @ X0))),
% 2.11/2.31      inference('sup+', [status(thm)], ['99', '100'])).
% 2.11/2.31  thf('102', plain,
% 2.11/2.31      (![X24 : $i, X25 : $i]:
% 2.11/2.31         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 2.11/2.31          | ~ (v1_relat_1 @ X25))),
% 2.11/2.31      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.11/2.31  thf('103', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.11/2.31           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.11/2.31      inference('sup-', [status(thm)], ['80', '85'])).
% 2.11/2.31  thf('104', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.11/2.31           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.11/2.31      inference('sup-', [status(thm)], ['80', '85'])).
% 2.11/2.31  thf('105', plain,
% 2.11/2.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X13)
% 2.11/2.31          | ((k5_relat_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 2.11/2.31              = (k5_relat_1 @ X14 @ (k5_relat_1 @ X13 @ X15)))
% 2.11/2.31          | ~ (v1_relat_1 @ X15)
% 2.11/2.31          | ~ (v1_relat_1 @ X14))),
% 2.11/2.31      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.11/2.31  thf('106', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 2.11/2.31            = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.11/2.31               (k5_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.11/2.31          | ~ (v1_relat_1 @ X2)
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['104', '105'])).
% 2.11/2.31  thf('107', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('108', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('109', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 2.11/2.31            = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.11/2.31               (k5_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 2.11/2.31          | ~ (v1_relat_1 @ X2))),
% 2.11/2.31      inference('demod', [status(thm)], ['106', '107', '108'])).
% 2.11/2.31  thf('110', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         (((k5_relat_1 @ 
% 2.11/2.31            (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)) @ 
% 2.11/2.31            (k6_relat_1 @ X1))
% 2.11/2.31            = (k5_relat_1 @ 
% 2.11/2.31               (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)) @ 
% 2.11/2.31               (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['103', '109'])).
% 2.11/2.31  thf('111', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.11/2.31           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.11/2.31      inference('sup-', [status(thm)], ['80', '85'])).
% 2.11/2.31  thf('112', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('113', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         ((k5_relat_1 @ 
% 2.11/2.31           (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)) @ 
% 2.11/2.31           (k6_relat_1 @ X1))
% 2.11/2.31           = (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 2.11/2.31      inference('demod', [status(thm)], ['110', '111', '112'])).
% 2.11/2.31  thf('114', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         (((k7_relat_1 @ (k6_relat_1 @ X2) @ 
% 2.11/2.31            (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 2.11/2.31            = (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['102', '113'])).
% 2.11/2.31  thf('115', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('116', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k6_relat_1 @ X2) @ 
% 2.11/2.31           (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 2.11/2.31           = (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 2.11/2.31      inference('demod', [status(thm)], ['114', '115'])).
% 2.11/2.31  thf('117', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.11/2.31           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 2.11/2.31           = (k6_relat_1 @ 
% 2.11/2.31              (k3_xboole_0 @ 
% 2.11/2.31               (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.11/2.31               X2)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['101', '116'])).
% 2.11/2.31  thf('118', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.11/2.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.11/2.31  thf('119', plain,
% 2.11/2.31      (![X24 : $i, X25 : $i]:
% 2.11/2.31         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 2.11/2.31          | ~ (v1_relat_1 @ X25))),
% 2.11/2.31      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.11/2.31  thf('120', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.11/2.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.11/2.31  thf('121', plain,
% 2.11/2.31      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 2.11/2.31      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.11/2.31  thf('122', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.11/2.31      inference('sup+', [status(thm)], ['120', '121'])).
% 2.11/2.31  thf('123', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (~ (r1_tarski @ X0 @ X1)
% 2.11/2.31          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.11/2.31              = (k6_relat_1 @ X0)))),
% 2.11/2.31      inference('demod', [status(thm)], ['83', '84'])).
% 2.11/2.31  thf('124', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.11/2.31           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.11/2.31      inference('sup-', [status(thm)], ['122', '123'])).
% 2.11/2.31  thf('125', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.11/2.31            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['119', '124'])).
% 2.11/2.31  thf('126', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('127', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.11/2.31           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.11/2.31      inference('demod', [status(thm)], ['125', '126'])).
% 2.11/2.31  thf('128', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.11/2.31           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['118', '127'])).
% 2.11/2.31  thf('129', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k3_xboole_0 @ X1 @ X0)
% 2.11/2.31           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.11/2.31      inference('demod', [status(thm)], ['96', '97', '98'])).
% 2.11/2.31  thf('130', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         ((k6_relat_1 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 2.11/2.31           = (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)))),
% 2.11/2.31      inference('demod', [status(thm)], ['117', '128', '129'])).
% 2.11/2.31  thf('131', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 2.11/2.31      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.11/2.31  thf('132', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         ((k1_relat_1 @ 
% 2.11/2.31           (k6_relat_1 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))
% 2.11/2.31           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 2.11/2.31      inference('sup+', [status(thm)], ['130', '131'])).
% 2.11/2.31  thf('133', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 2.11/2.31      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.11/2.31  thf('134', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.11/2.31           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 2.11/2.31      inference('demod', [status(thm)], ['132', '133'])).
% 2.11/2.31  thf('135', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k3_xboole_0 @ X1 @ X0)
% 2.11/2.31           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.11/2.31      inference('demod', [status(thm)], ['91', '92'])).
% 2.11/2.31  thf('136', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('137', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.11/2.31           = (k3_xboole_0 @ X1 @ X0))),
% 2.11/2.31      inference('demod', [status(thm)], ['77', '134', '135', '136'])).
% 2.11/2.31  thf('138', plain,
% 2.11/2.31      (![X18 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X18)) @ X18) = (X18))
% 2.11/2.31          | ~ (v1_relat_1 @ X18))),
% 2.11/2.31      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.11/2.31  thf('139', plain,
% 2.11/2.31      (![X24 : $i, X25 : $i]:
% 2.11/2.31         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 2.11/2.31          | ~ (v1_relat_1 @ X25))),
% 2.11/2.31      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.11/2.31  thf('140', plain,
% 2.11/2.31      (![X0 : $i]:
% 2.11/2.31         (((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0))
% 2.11/2.31          | ~ (v1_relat_1 @ X0)
% 2.11/2.31          | ~ (v1_relat_1 @ X0))),
% 2.11/2.31      inference('sup+', [status(thm)], ['138', '139'])).
% 2.11/2.31  thf('141', plain,
% 2.11/2.31      (![X0 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 2.11/2.31      inference('simplify', [status(thm)], ['140'])).
% 2.11/2.31  thf('142', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k7_relat_1 @ 
% 2.11/2.31            (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ 
% 2.11/2.31            (k3_xboole_0 @ X1 @ X0))
% 2.11/2.31            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.11/2.31          | ~ (v1_relat_1 @ 
% 2.11/2.31               (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 2.11/2.31      inference('sup+', [status(thm)], ['137', '141'])).
% 2.11/2.31  thf('143', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.11/2.31      inference('demod', [status(thm)], ['70', '71'])).
% 2.11/2.31  thf('144', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ 
% 2.11/2.31           (k3_xboole_0 @ X1 @ X0))
% 2.11/2.31           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 2.11/2.31      inference('demod', [status(thm)], ['142', '143'])).
% 2.11/2.31  thf('145', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.11/2.31            (k3_xboole_0 @ X0 @ X1))
% 2.11/2.31            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['5', '144'])).
% 2.11/2.31  thf('146', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.11/2.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.11/2.31  thf('147', plain,
% 2.11/2.31      (![X24 : $i, X25 : $i]:
% 2.11/2.31         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 2.11/2.31          | ~ (v1_relat_1 @ X25))),
% 2.11/2.31      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.11/2.31  thf('148', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.11/2.31           = (k3_xboole_0 @ X0 @ X1))),
% 2.11/2.31      inference('demod', [status(thm)], ['48', '49'])).
% 2.11/2.31  thf('149', plain,
% 2.11/2.31      (![X18 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X18)) @ X18) = (X18))
% 2.11/2.31          | ~ (v1_relat_1 @ X18))),
% 2.11/2.31      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.11/2.31  thf('150', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.11/2.31            (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.11/2.31            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['148', '149'])).
% 2.11/2.31  thf('151', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.11/2.31      inference('demod', [status(thm)], ['73', '74'])).
% 2.11/2.31  thf('152', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.11/2.31           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.11/2.31           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.11/2.31      inference('demod', [status(thm)], ['150', '151'])).
% 2.11/2.31  thf('153', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.11/2.31            (k3_xboole_0 @ X1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['147', '152'])).
% 2.11/2.31  thf('154', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.11/2.31      inference('demod', [status(thm)], ['73', '74'])).
% 2.11/2.31  thf('155', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.11/2.31           (k3_xboole_0 @ X1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.11/2.31      inference('demod', [status(thm)], ['153', '154'])).
% 2.11/2.31  thf('156', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 2.11/2.31           (k3_xboole_0 @ X1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 2.11/2.31      inference('sup+', [status(thm)], ['146', '155'])).
% 2.11/2.31  thf('157', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('158', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.11/2.31           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.11/2.31      inference('demod', [status(thm)], ['145', '156', '157'])).
% 2.11/2.31  thf('159', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ X2)
% 2.11/2.31          | ~ (v1_relat_1 @ X1)
% 2.11/2.31          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.11/2.31              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 2.11/2.31      inference('simplify', [status(thm)], ['60'])).
% 2.11/2.31  thf('160', plain,
% 2.11/2.31      (![X18 : $i]:
% 2.11/2.31         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X18)) @ X18) = (X18))
% 2.11/2.31          | ~ (v1_relat_1 @ X18))),
% 2.11/2.31      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.11/2.31  thf('161', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (((k5_relat_1 @ 
% 2.11/2.31            (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0)
% 2.11/2.31            = (k5_relat_1 @ X1 @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ X1)
% 2.11/2.31          | ~ (v1_relat_1 @ X0)
% 2.11/2.31          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['159', '160'])).
% 2.11/2.31  thf('162', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.11/2.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.11/2.31          | ((k5_relat_1 @ 
% 2.11/2.31              (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.11/2.31               (k1_relat_1 @ 
% 2.11/2.31                (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))) @ 
% 2.11/2.31              (k6_relat_1 @ X1))
% 2.11/2.31              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 2.11/2.31      inference('sup-', [status(thm)], ['158', '161'])).
% 2.11/2.31  thf('163', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.11/2.31      inference('demod', [status(thm)], ['73', '74'])).
% 2.11/2.31  thf('164', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('165', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.11/2.31      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.11/2.31  thf('166', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.11/2.31           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.11/2.31      inference('demod', [status(thm)], ['145', '156', '157'])).
% 2.11/2.31  thf('167', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.11/2.31           = (k3_xboole_0 @ X1 @ X0))),
% 2.11/2.31      inference('demod', [status(thm)], ['77', '134', '135', '136'])).
% 2.11/2.31  thf('168', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.11/2.31           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.11/2.31      inference('demod', [status(thm)], ['145', '156', '157'])).
% 2.11/2.31  thf('169', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.11/2.31           = (k3_xboole_0 @ X1 @ X0))),
% 2.11/2.31      inference('demod', [status(thm)], ['167', '168'])).
% 2.11/2.31  thf('170', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.11/2.31           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['118', '127'])).
% 2.11/2.31  thf('171', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.11/2.31           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.11/2.31      inference('demod', [status(thm)], ['145', '156', '157'])).
% 2.11/2.31  thf('172', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.11/2.31           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.11/2.31      inference('sup+', [status(thm)], ['118', '127'])).
% 2.11/2.31  thf('173', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.11/2.31           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.11/2.31      inference('demod', [status(thm)], ['145', '156', '157'])).
% 2.11/2.31  thf('174', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 2.11/2.31           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.11/2.31      inference('demod', [status(thm)],
% 2.11/2.31                ['162', '163', '164', '165', '166', '169', '170', '171', 
% 2.11/2.31                 '172', '173'])).
% 2.11/2.31  thf('175', plain,
% 2.11/2.31      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.11/2.31         != (k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A))),
% 2.11/2.31      inference('demod', [status(thm)], ['4', '174'])).
% 2.11/2.31  thf('176', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.11/2.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.11/2.31  thf('177', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 2.11/2.31           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.11/2.31      inference('demod', [status(thm)],
% 2.11/2.31                ['162', '163', '164', '165', '166', '169', '170', '171', 
% 2.11/2.31                 '172', '173'])).
% 2.11/2.31  thf('178', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 2.11/2.31           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.11/2.31      inference('sup+', [status(thm)], ['176', '177'])).
% 2.11/2.31  thf('179', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 2.11/2.31           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.11/2.31      inference('demod', [status(thm)],
% 2.11/2.31                ['162', '163', '164', '165', '166', '169', '170', '171', 
% 2.11/2.31                 '172', '173'])).
% 2.11/2.31  thf('180', plain,
% 2.11/2.31      (![X0 : $i, X1 : $i]:
% 2.11/2.31         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.11/2.31           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 2.11/2.31      inference('sup+', [status(thm)], ['178', '179'])).
% 2.11/2.31  thf('181', plain,
% 2.11/2.31      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.11/2.31         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 2.11/2.31      inference('demod', [status(thm)], ['175', '180'])).
% 2.11/2.31  thf('182', plain, ($false), inference('simplify', [status(thm)], ['181'])).
% 2.11/2.31  
% 2.11/2.31  % SZS output end Refutation
% 2.11/2.31  
% 2.11/2.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
