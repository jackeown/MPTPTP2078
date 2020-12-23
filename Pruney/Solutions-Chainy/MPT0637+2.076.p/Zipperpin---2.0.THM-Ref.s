%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1rilo2zDfa

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:07 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  154 (2793 expanded)
%              Number of leaves         :   24 ( 999 expanded)
%              Depth                    :   26
%              Number of atoms          : 1366 (24621 expanded)
%              Number of equality atoms :  106 (1827 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k8_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X12 @ X11 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X11 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k8_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X22: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X22 ) )
      = ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X18 ) @ ( k4_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X22: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X22 ) )
      = ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('14',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k8_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k8_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('24',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('25',plain,(
    ! [X25: $i] :
      ( ( ( k5_relat_1 @ X25 @ ( k6_relat_1 @ ( k2_relat_1 @ X25 ) ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k8_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t139_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) )
            = ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k8_relat_1 @ X17 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k5_relat_1 @ X16 @ ( k8_relat_1 @ X17 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','38'])).

thf('40',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X12 @ X11 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X11 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('45',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k8_relat_1 @ X17 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k5_relat_1 @ X16 @ ( k8_relat_1 @ X17 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k8_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('55',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('56',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k8_relat_1 @ X17 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k5_relat_1 @ X16 @ ( k8_relat_1 @ X17 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('61',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['43','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','64'])).

thf('66',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('67',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X12 @ X11 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X11 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('73',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','74'])).

thf('76',plain,(
    ! [X25: $i] :
      ( ( ( k5_relat_1 @ X25 @ ( k6_relat_1 @ ( k2_relat_1 @ X25 ) ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('77',plain,(
    ! [X22: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X22 ) )
      = ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('78',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X18 ) @ ( k4_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['75','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('88',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k8_relat_1 @ X17 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k5_relat_1 @ X16 @ ( k8_relat_1 @ X17 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('91',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','62'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['84','85','86','92','93'])).

thf('95',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X12 @ X11 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X11 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','74'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','74'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('100',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k8_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('102',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('103',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ( ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['100','107'])).

thf('109',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X12 @ X11 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X11 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('114',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('115',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','62'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['84','85','86','92','93'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','116','117'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','126'])).

thf('128',plain,(
    $false ),
    inference(simplify,[status(thm)],['127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1rilo2zDfa
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.68  % Solved by: fo/fo7.sh
% 0.48/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.68  % done 326 iterations in 0.196s
% 0.48/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.68  % SZS output start Refutation
% 0.48/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.48/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.68  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.48/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.68  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.48/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.48/0.68  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.48/0.68  thf(t123_relat_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( v1_relat_1 @ B ) =>
% 0.48/0.68       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.48/0.68  thf('0', plain,
% 0.48/0.68      (![X13 : $i, X14 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X14 @ X13) = (k5_relat_1 @ X13 @ (k6_relat_1 @ X14)))
% 0.48/0.68          | ~ (v1_relat_1 @ X13))),
% 0.48/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.48/0.68  thf(t43_funct_1, conjecture,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.48/0.68       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.68    (~( ![A:$i,B:$i]:
% 0.48/0.68        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.48/0.68          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.48/0.68    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.48/0.68  thf('1', plain,
% 0.48/0.68      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.48/0.68         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('2', plain,
% 0.48/0.68      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.48/0.68          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.48/0.68        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.48/0.68  thf(fc3_funct_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.48/0.68       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.48/0.68  thf('3', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('4', plain,
% 0.48/0.68      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.48/0.68         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('demod', [status(thm)], ['2', '3'])).
% 0.48/0.68  thf(t119_relat_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( v1_relat_1 @ B ) =>
% 0.48/0.68       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.48/0.68         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.48/0.68  thf('5', plain,
% 0.48/0.68      (![X11 : $i, X12 : $i]:
% 0.48/0.68         (((k2_relat_1 @ (k8_relat_1 @ X12 @ X11))
% 0.48/0.68            = (k3_xboole_0 @ (k2_relat_1 @ X11) @ X12))
% 0.48/0.68          | ~ (v1_relat_1 @ X11))),
% 0.48/0.68      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.48/0.68  thf('6', plain,
% 0.48/0.68      (![X13 : $i, X14 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X14 @ X13) = (k5_relat_1 @ X13 @ (k6_relat_1 @ X14)))
% 0.48/0.68          | ~ (v1_relat_1 @ X13))),
% 0.48/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.48/0.68  thf(t72_relat_1, axiom,
% 0.48/0.68    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.48/0.68  thf('7', plain,
% 0.48/0.68      (![X22 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X22)) = (k6_relat_1 @ X22))),
% 0.48/0.68      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.48/0.68  thf(t54_relat_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( v1_relat_1 @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( v1_relat_1 @ B ) =>
% 0.48/0.68           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.48/0.68             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.48/0.68  thf('8', plain,
% 0.48/0.68      (![X18 : $i, X19 : $i]:
% 0.48/0.68         (~ (v1_relat_1 @ X18)
% 0.48/0.68          | ((k4_relat_1 @ (k5_relat_1 @ X19 @ X18))
% 0.48/0.68              = (k5_relat_1 @ (k4_relat_1 @ X18) @ (k4_relat_1 @ X19)))
% 0.48/0.68          | ~ (v1_relat_1 @ X19))),
% 0.48/0.68      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.48/0.68  thf('9', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.48/0.68            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.68          | ~ (v1_relat_1 @ X1))),
% 0.48/0.68      inference('sup+', [status(thm)], ['7', '8'])).
% 0.48/0.68  thf('10', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('11', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.48/0.68            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.48/0.68          | ~ (v1_relat_1 @ X1))),
% 0.48/0.68      inference('demod', [status(thm)], ['9', '10'])).
% 0.48/0.68  thf('12', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68            = (k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X1)) @ 
% 0.48/0.68               (k6_relat_1 @ X0)))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['6', '11'])).
% 0.48/0.68  thf('13', plain,
% 0.48/0.68      (![X22 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X22)) = (k6_relat_1 @ X22))),
% 0.48/0.68      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.48/0.68  thf('14', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('15', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('16', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.48/0.68  thf('17', plain,
% 0.48/0.68      (![X13 : $i, X14 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X14 @ X13) = (k5_relat_1 @ X13 @ (k6_relat_1 @ X14)))
% 0.48/0.68          | ~ (v1_relat_1 @ X13))),
% 0.48/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.48/0.68  thf('18', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.48/0.68  thf('19', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.48/0.68            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['17', '18'])).
% 0.48/0.68  thf('20', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('21', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.48/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['19', '20'])).
% 0.48/0.68  thf('22', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.48/0.68           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['16', '21'])).
% 0.48/0.68  thf('23', plain,
% 0.48/0.68      (![X13 : $i, X14 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X14 @ X13) = (k5_relat_1 @ X13 @ (k6_relat_1 @ X14)))
% 0.48/0.68          | ~ (v1_relat_1 @ X13))),
% 0.48/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.48/0.68  thf(t71_relat_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.48/0.68       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.48/0.68  thf('24', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.48/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.48/0.68  thf(t80_relat_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( v1_relat_1 @ A ) =>
% 0.48/0.68       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.48/0.68  thf('25', plain,
% 0.48/0.68      (![X25 : $i]:
% 0.48/0.68         (((k5_relat_1 @ X25 @ (k6_relat_1 @ (k2_relat_1 @ X25))) = (X25))
% 0.48/0.68          | ~ (v1_relat_1 @ X25))),
% 0.48/0.68      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.48/0.68  thf('26', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.48/0.68            = (k6_relat_1 @ X0))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['24', '25'])).
% 0.48/0.68  thf('27', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('28', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.48/0.68           = (k6_relat_1 @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.48/0.68  thf('29', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['23', '28'])).
% 0.48/0.68  thf('30', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('31', plain,
% 0.48/0.68      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['29', '30'])).
% 0.48/0.68  thf('32', plain,
% 0.48/0.68      (![X13 : $i, X14 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X14 @ X13) = (k5_relat_1 @ X13 @ (k6_relat_1 @ X14)))
% 0.48/0.68          | ~ (v1_relat_1 @ X13))),
% 0.48/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.48/0.68  thf(t139_relat_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( v1_relat_1 @ B ) =>
% 0.48/0.68       ( ![C:$i]:
% 0.48/0.68         ( ( v1_relat_1 @ C ) =>
% 0.48/0.68           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 0.48/0.68             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.48/0.68  thf('33', plain,
% 0.48/0.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.48/0.68         (~ (v1_relat_1 @ X15)
% 0.48/0.68          | ((k8_relat_1 @ X17 @ (k5_relat_1 @ X16 @ X15))
% 0.48/0.68              = (k5_relat_1 @ X16 @ (k8_relat_1 @ X17 @ X15)))
% 0.48/0.68          | ~ (v1_relat_1 @ X16))),
% 0.48/0.68      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.48/0.68  thf('34', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.48/0.68            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 0.48/0.68          | ~ (v1_relat_1 @ X0)
% 0.48/0.68          | ~ (v1_relat_1 @ X0)
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['32', '33'])).
% 0.48/0.68  thf('35', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('36', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.48/0.68            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 0.48/0.68          | ~ (v1_relat_1 @ X0)
% 0.48/0.68          | ~ (v1_relat_1 @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['34', '35'])).
% 0.48/0.68  thf('37', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         (~ (v1_relat_1 @ X0)
% 0.48/0.68          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.48/0.68              = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)))))),
% 0.48/0.68      inference('simplify', [status(thm)], ['36'])).
% 0.48/0.68  thf('38', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ X1))
% 0.48/0.68            = (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68          | ~ (v1_relat_1 @ X1))),
% 0.48/0.68      inference('sup+', [status(thm)], ['31', '37'])).
% 0.48/0.68  thf('39', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['22', '38'])).
% 0.48/0.68  thf('40', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('41', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k8_relat_1 @ X1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['39', '40'])).
% 0.48/0.68  thf('42', plain,
% 0.48/0.68      (![X11 : $i, X12 : $i]:
% 0.48/0.68         (((k2_relat_1 @ (k8_relat_1 @ X12 @ X11))
% 0.48/0.68            = (k3_xboole_0 @ (k2_relat_1 @ X11) @ X12))
% 0.48/0.68          | ~ (v1_relat_1 @ X11))),
% 0.48/0.68      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.48/0.68  thf('43', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68            = (k3_xboole_0 @ 
% 0.48/0.68               (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1))
% 0.48/0.68          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['41', '42'])).
% 0.48/0.68  thf('44', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.48/0.68           = (k6_relat_1 @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.48/0.68  thf('45', plain,
% 0.48/0.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.48/0.68         (~ (v1_relat_1 @ X15)
% 0.48/0.68          | ((k8_relat_1 @ X17 @ (k5_relat_1 @ X16 @ X15))
% 0.48/0.68              = (k5_relat_1 @ X16 @ (k8_relat_1 @ X17 @ X15)))
% 0.48/0.68          | ~ (v1_relat_1 @ X16))),
% 0.48/0.68      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.48/0.68  thf('46', plain,
% 0.48/0.68      (![X13 : $i, X14 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X14 @ X13) = (k5_relat_1 @ X13 @ (k6_relat_1 @ X14)))
% 0.48/0.68          | ~ (v1_relat_1 @ X13))),
% 0.48/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.48/0.68  thf(dt_k5_relat_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.48/0.68       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.48/0.68  thf('47', plain,
% 0.48/0.68      (![X9 : $i, X10 : $i]:
% 0.48/0.68         (~ (v1_relat_1 @ X9)
% 0.48/0.68          | ~ (v1_relat_1 @ X10)
% 0.48/0.68          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.48/0.68  thf('48', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.48/0.68          | ~ (v1_relat_1 @ X0)
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.48/0.68          | ~ (v1_relat_1 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['46', '47'])).
% 0.48/0.68  thf('49', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('50', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.48/0.68          | ~ (v1_relat_1 @ X0)
% 0.48/0.68          | ~ (v1_relat_1 @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['48', '49'])).
% 0.48/0.68  thf('51', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['50'])).
% 0.48/0.68  thf('52', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)))
% 0.48/0.68          | ~ (v1_relat_1 @ X2)
% 0.48/0.68          | ~ (v1_relat_1 @ X0)
% 0.48/0.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['45', '51'])).
% 0.48/0.68  thf('53', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.68          | (v1_relat_1 @ 
% 0.48/0.68             (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.48/0.68              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['44', '52'])).
% 0.48/0.68  thf('54', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('55', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('56', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('57', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.48/0.68           = (k6_relat_1 @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.48/0.68  thf('58', plain,
% 0.48/0.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.48/0.68         (~ (v1_relat_1 @ X15)
% 0.48/0.68          | ((k8_relat_1 @ X17 @ (k5_relat_1 @ X16 @ X15))
% 0.48/0.68              = (k5_relat_1 @ X16 @ (k8_relat_1 @ X17 @ X15)))
% 0.48/0.68          | ~ (v1_relat_1 @ X16))),
% 0.48/0.68      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.48/0.68  thf('59', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.48/0.68            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.48/0.68               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['57', '58'])).
% 0.48/0.68  thf('60', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('61', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('62', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.48/0.68           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.48/0.68              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.48/0.68      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.48/0.68  thf('63', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['53', '54', '55', '56', '62'])).
% 0.48/0.68  thf('64', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68           = (k3_xboole_0 @ 
% 0.48/0.68              (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1))),
% 0.48/0.68      inference('demod', [status(thm)], ['43', '63'])).
% 0.48/0.68  thf('65', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.48/0.68            = (k3_xboole_0 @ 
% 0.48/0.68               (k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ X0) @ X0))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['5', '64'])).
% 0.48/0.68  thf('66', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.48/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.48/0.68  thf('67', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('68', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.48/0.68           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.48/0.68  thf('69', plain,
% 0.48/0.68      (![X11 : $i, X12 : $i]:
% 0.48/0.68         (((k2_relat_1 @ (k8_relat_1 @ X12 @ X11))
% 0.48/0.68            = (k3_xboole_0 @ (k2_relat_1 @ X11) @ X12))
% 0.48/0.68          | ~ (v1_relat_1 @ X11))),
% 0.48/0.68      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.48/0.68  thf('70', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.48/0.68           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.48/0.68  thf('71', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ X0)
% 0.48/0.68            = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['69', '70'])).
% 0.48/0.68  thf('72', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.48/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.48/0.68  thf('73', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('74', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k3_xboole_0 @ X1 @ X0)
% 0.48/0.68           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.48/0.68  thf('75', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.48/0.68           = (k3_xboole_0 @ X1 @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['68', '74'])).
% 0.48/0.68  thf('76', plain,
% 0.48/0.68      (![X25 : $i]:
% 0.48/0.68         (((k5_relat_1 @ X25 @ (k6_relat_1 @ (k2_relat_1 @ X25))) = (X25))
% 0.48/0.68          | ~ (v1_relat_1 @ X25))),
% 0.48/0.68      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.48/0.68  thf('77', plain,
% 0.48/0.68      (![X22 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X22)) = (k6_relat_1 @ X22))),
% 0.48/0.68      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.48/0.68  thf('78', plain,
% 0.48/0.68      (![X18 : $i, X19 : $i]:
% 0.48/0.68         (~ (v1_relat_1 @ X18)
% 0.48/0.68          | ((k4_relat_1 @ (k5_relat_1 @ X19 @ X18))
% 0.48/0.68              = (k5_relat_1 @ (k4_relat_1 @ X18) @ (k4_relat_1 @ X19)))
% 0.48/0.68          | ~ (v1_relat_1 @ X19))),
% 0.48/0.68      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.48/0.68  thf('79', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.48/0.68          | ~ (v1_relat_1 @ X1)
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['77', '78'])).
% 0.48/0.68  thf('80', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('81', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.48/0.68          | ~ (v1_relat_1 @ X1))),
% 0.48/0.68      inference('demod', [status(thm)], ['79', '80'])).
% 0.48/0.68  thf('82', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (((k4_relat_1 @ X0)
% 0.48/0.68            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 0.48/0.68               (k4_relat_1 @ X0)))
% 0.48/0.68          | ~ (v1_relat_1 @ X0)
% 0.48/0.68          | ~ (v1_relat_1 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['76', '81'])).
% 0.48/0.68  thf('83', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (v1_relat_1 @ X0)
% 0.48/0.68          | ((k4_relat_1 @ X0)
% 0.48/0.68              = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 0.48/0.68                 (k4_relat_1 @ X0))))),
% 0.48/0.68      inference('simplify', [status(thm)], ['82'])).
% 0.48/0.68  thf('84', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.48/0.68            = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.48/0.68               (k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))))
% 0.48/0.68          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['75', '83'])).
% 0.48/0.68  thf('85', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.48/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['19', '20'])).
% 0.48/0.68  thf('86', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.48/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['19', '20'])).
% 0.48/0.68  thf('87', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.48/0.68           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['16', '21'])).
% 0.48/0.68  thf('88', plain,
% 0.48/0.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.48/0.68         (~ (v1_relat_1 @ X15)
% 0.48/0.68          | ((k8_relat_1 @ X17 @ (k5_relat_1 @ X16 @ X15))
% 0.48/0.68              = (k5_relat_1 @ X16 @ (k8_relat_1 @ X17 @ X15)))
% 0.48/0.68          | ~ (v1_relat_1 @ X16))),
% 0.48/0.68      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.48/0.68  thf('89', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.48/0.68               (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['87', '88'])).
% 0.48/0.68  thf('90', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('91', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('92', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.48/0.68              (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))),
% 0.48/0.68      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.48/0.68  thf('93', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['53', '54', '55', '56', '62'])).
% 0.48/0.68  thf('94', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.48/0.68           = (k8_relat_1 @ X1 @ 
% 0.48/0.68              (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))))),
% 0.48/0.68      inference('demod', [status(thm)], ['84', '85', '86', '92', '93'])).
% 0.48/0.68  thf('95', plain,
% 0.48/0.68      (![X11 : $i, X12 : $i]:
% 0.48/0.68         (((k2_relat_1 @ (k8_relat_1 @ X12 @ X11))
% 0.48/0.68            = (k3_xboole_0 @ (k2_relat_1 @ X11) @ X12))
% 0.48/0.68          | ~ (v1_relat_1 @ X11))),
% 0.48/0.68      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.48/0.68  thf('96', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.68            = (k3_xboole_0 @ 
% 0.48/0.68               (k2_relat_1 @ 
% 0.48/0.68                (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))) @ 
% 0.48/0.68               X1))
% 0.48/0.68          | ~ (v1_relat_1 @ 
% 0.48/0.68               (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['94', '95'])).
% 0.48/0.68  thf('97', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.48/0.68           = (k3_xboole_0 @ X1 @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['68', '74'])).
% 0.48/0.68  thf('98', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.48/0.68           = (k3_xboole_0 @ X1 @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['68', '74'])).
% 0.48/0.68  thf('99', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k3_xboole_0 @ X1 @ X0)
% 0.48/0.68           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.48/0.68  thf('100', plain,
% 0.48/0.68      (![X13 : $i, X14 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X14 @ X13) = (k5_relat_1 @ X13 @ (k6_relat_1 @ X14)))
% 0.48/0.68          | ~ (v1_relat_1 @ X13))),
% 0.48/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.48/0.68  thf(t17_xboole_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.48/0.68  thf('101', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.48/0.68      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.48/0.68  thf('102', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.48/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.48/0.68  thf(t79_relat_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( v1_relat_1 @ B ) =>
% 0.48/0.68       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.48/0.68         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.48/0.68  thf('103', plain,
% 0.48/0.68      (![X23 : $i, X24 : $i]:
% 0.48/0.68         (~ (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 0.48/0.68          | ((k5_relat_1 @ X23 @ (k6_relat_1 @ X24)) = (X23))
% 0.48/0.68          | ~ (v1_relat_1 @ X23))),
% 0.48/0.68      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.48/0.68  thf('104', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (r1_tarski @ X0 @ X1)
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.68          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.48/0.68              = (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['102', '103'])).
% 0.48/0.68  thf('105', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('106', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (r1_tarski @ X0 @ X1)
% 0.48/0.68          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.48/0.68              = (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['104', '105'])).
% 0.48/0.68  thf('107', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.48/0.68           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['101', '106'])).
% 0.48/0.68  thf('108', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.48/0.68            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['100', '107'])).
% 0.48/0.68  thf('109', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('110', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.48/0.68           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['108', '109'])).
% 0.48/0.68  thf('111', plain,
% 0.48/0.68      (![X11 : $i, X12 : $i]:
% 0.48/0.68         (((k2_relat_1 @ (k8_relat_1 @ X12 @ X11))
% 0.48/0.68            = (k3_xboole_0 @ (k2_relat_1 @ X11) @ X12))
% 0.48/0.68          | ~ (v1_relat_1 @ X11))),
% 0.48/0.68      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.48/0.68  thf('112', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.48/0.68            = (k3_xboole_0 @ 
% 0.48/0.68               (k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ X1))
% 0.48/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['110', '111'])).
% 0.48/0.68  thf('113', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.48/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.48/0.68  thf('114', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.48/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.48/0.68  thf('115', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.48/0.68  thf('116', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k3_xboole_0 @ X1 @ X0)
% 0.48/0.68           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.48/0.68      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 0.48/0.68  thf('117', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['53', '54', '55', '56', '62'])).
% 0.48/0.68  thf('118', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['96', '97', '98', '99', '116', '117'])).
% 0.48/0.68  thf('119', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.48/0.68           = (k8_relat_1 @ X1 @ 
% 0.48/0.68              (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))))),
% 0.48/0.68      inference('demod', [status(thm)], ['84', '85', '86', '92', '93'])).
% 0.48/0.68  thf('120', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.48/0.68           = (k8_relat_1 @ X0 @ 
% 0.48/0.68              (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['118', '119'])).
% 0.48/0.68  thf('121', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.48/0.68           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.69      inference('demod', [status(thm)], ['108', '109'])).
% 0.48/0.69  thf('122', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.48/0.69           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.48/0.69      inference('demod', [status(thm)], ['120', '121'])).
% 0.48/0.69  thf('123', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['96', '97', '98', '99', '116', '117'])).
% 0.48/0.69  thf('124', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.48/0.69           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.69      inference('demod', [status(thm)], ['108', '109'])).
% 0.48/0.69  thf('125', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.48/0.69           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['123', '124'])).
% 0.48/0.69  thf('126', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.48/0.69           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['122', '125'])).
% 0.48/0.69  thf('127', plain,
% 0.48/0.69      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.48/0.69         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.48/0.69      inference('demod', [status(thm)], ['4', '126'])).
% 0.48/0.69  thf('128', plain, ($false), inference('simplify', [status(thm)], ['127'])).
% 0.48/0.69  
% 0.48/0.69  % SZS output end Refutation
% 0.48/0.69  
% 0.48/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
