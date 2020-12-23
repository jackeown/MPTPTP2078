%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0R5eSNuHyO

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:01 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 542 expanded)
%              Number of leaves         :   27 ( 202 expanded)
%              Depth                    :   16
%              Number of atoms          : 1013 (4542 expanded)
%              Number of equality atoms :   75 ( 333 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X29 )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('10',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('11',plain,(
    ! [X31: $i] :
      ( ( ( k5_relat_1 @ X31 @ ( k6_relat_1 @ ( k2_relat_1 @ X31 ) ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k5_relat_1 @ X23 @ ( k5_relat_1 @ X22 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X29 )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X27 ) @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('42',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( ( k8_relat_1 @ X21 @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) )
      = ( k6_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('51',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X1 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X1 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('66',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','63','64','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','67'])).

thf('69',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('70',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k5_relat_1 @ X23 @ ( k5_relat_1 @ X22 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('76',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('77',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','67'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','67'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['81','82','87','88','89'])).

thf('91',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','90'])).

thf('92',plain,(
    $false ),
    inference(simplify,[status(thm)],['91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0R5eSNuHyO
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.37/1.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.37/1.59  % Solved by: fo/fo7.sh
% 1.37/1.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.59  % done 1814 iterations in 1.138s
% 1.37/1.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.37/1.59  % SZS output start Refutation
% 1.37/1.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.37/1.59  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.59  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.37/1.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.37/1.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.37/1.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.37/1.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.37/1.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.37/1.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.37/1.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.37/1.59  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.37/1.59  thf(t123_relat_1, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( v1_relat_1 @ B ) =>
% 1.37/1.59       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 1.37/1.59  thf('0', plain,
% 1.37/1.59      (![X18 : $i, X19 : $i]:
% 1.37/1.59         (((k8_relat_1 @ X19 @ X18) = (k5_relat_1 @ X18 @ (k6_relat_1 @ X19)))
% 1.37/1.59          | ~ (v1_relat_1 @ X18))),
% 1.37/1.59      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.37/1.59  thf(t43_funct_1, conjecture,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.37/1.59       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.37/1.59  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.59    (~( ![A:$i,B:$i]:
% 1.37/1.59        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.37/1.59          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 1.37/1.59    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 1.37/1.59  thf('1', plain,
% 1.37/1.59      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 1.37/1.59         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.37/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.59  thf('2', plain,
% 1.37/1.59      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 1.37/1.59          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 1.37/1.59        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 1.37/1.59      inference('sup-', [status(thm)], ['0', '1'])).
% 1.37/1.59  thf(fc3_funct_1, axiom,
% 1.37/1.59    (![A:$i]:
% 1.37/1.59     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.37/1.59       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.37/1.59  thf('3', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('4', plain,
% 1.37/1.59      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 1.37/1.59         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.37/1.59      inference('demod', [status(thm)], ['2', '3'])).
% 1.37/1.59  thf(d10_xboole_0, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.37/1.59  thf('5', plain,
% 1.37/1.59      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.37/1.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.37/1.59  thf('6', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.37/1.59      inference('simplify', [status(thm)], ['5'])).
% 1.37/1.59  thf(t77_relat_1, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( v1_relat_1 @ B ) =>
% 1.37/1.59       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.37/1.59         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 1.37/1.59  thf('7', plain,
% 1.37/1.59      (![X29 : $i, X30 : $i]:
% 1.37/1.59         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 1.37/1.59          | ((k5_relat_1 @ (k6_relat_1 @ X30) @ X29) = (X29))
% 1.37/1.59          | ~ (v1_relat_1 @ X29))),
% 1.37/1.59      inference('cnf', [status(esa)], [t77_relat_1])).
% 1.37/1.59  thf('8', plain,
% 1.37/1.59      (![X0 : $i]:
% 1.37/1.59         (~ (v1_relat_1 @ X0)
% 1.37/1.59          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 1.37/1.59      inference('sup-', [status(thm)], ['6', '7'])).
% 1.37/1.59  thf('9', plain,
% 1.37/1.59      (![X18 : $i, X19 : $i]:
% 1.37/1.59         (((k8_relat_1 @ X19 @ X18) = (k5_relat_1 @ X18 @ (k6_relat_1 @ X19)))
% 1.37/1.59          | ~ (v1_relat_1 @ X18))),
% 1.37/1.59      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.37/1.59  thf(t71_relat_1, axiom,
% 1.37/1.59    (![A:$i]:
% 1.37/1.59     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.37/1.59       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.37/1.59  thf('10', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 1.37/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.37/1.59  thf(t80_relat_1, axiom,
% 1.37/1.59    (![A:$i]:
% 1.37/1.59     ( ( v1_relat_1 @ A ) =>
% 1.37/1.59       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.37/1.59  thf('11', plain,
% 1.37/1.59      (![X31 : $i]:
% 1.37/1.59         (((k5_relat_1 @ X31 @ (k6_relat_1 @ (k2_relat_1 @ X31))) = (X31))
% 1.37/1.59          | ~ (v1_relat_1 @ X31))),
% 1.37/1.59      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.37/1.59  thf('12', plain,
% 1.37/1.59      (![X0 : $i]:
% 1.37/1.59         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.37/1.59            = (k6_relat_1 @ X0))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['10', '11'])).
% 1.37/1.59  thf('13', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('14', plain,
% 1.37/1.59      (![X0 : $i]:
% 1.37/1.59         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.37/1.59           = (k6_relat_1 @ X0))),
% 1.37/1.59      inference('demod', [status(thm)], ['12', '13'])).
% 1.37/1.59  thf(t55_relat_1, axiom,
% 1.37/1.59    (![A:$i]:
% 1.37/1.59     ( ( v1_relat_1 @ A ) =>
% 1.37/1.59       ( ![B:$i]:
% 1.37/1.59         ( ( v1_relat_1 @ B ) =>
% 1.37/1.59           ( ![C:$i]:
% 1.37/1.59             ( ( v1_relat_1 @ C ) =>
% 1.37/1.59               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.37/1.59                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.37/1.59  thf('15', plain,
% 1.37/1.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.37/1.59         (~ (v1_relat_1 @ X22)
% 1.37/1.59          | ((k5_relat_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 1.37/1.59              = (k5_relat_1 @ X23 @ (k5_relat_1 @ X22 @ X24)))
% 1.37/1.59          | ~ (v1_relat_1 @ X24)
% 1.37/1.59          | ~ (v1_relat_1 @ X23))),
% 1.37/1.59      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.37/1.59  thf('16', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.37/1.59            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.37/1.59               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.37/1.59          | ~ (v1_relat_1 @ X1)
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['14', '15'])).
% 1.37/1.59  thf('17', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('18', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('19', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.37/1.59            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.37/1.59               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.37/1.59          | ~ (v1_relat_1 @ X1))),
% 1.37/1.59      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.37/1.59  thf('20', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 1.37/1.59            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.37/1.59               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['9', '19'])).
% 1.37/1.59  thf('21', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('22', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('23', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 1.37/1.59           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.37/1.59              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 1.37/1.59      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.37/1.59  thf('24', plain,
% 1.37/1.59      (![X18 : $i, X19 : $i]:
% 1.37/1.59         (((k8_relat_1 @ X19 @ X18) = (k5_relat_1 @ X18 @ (k6_relat_1 @ X19)))
% 1.37/1.59          | ~ (v1_relat_1 @ X18))),
% 1.37/1.59      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.37/1.59  thf(t94_relat_1, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( v1_relat_1 @ B ) =>
% 1.37/1.59       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.37/1.59  thf('25', plain,
% 1.37/1.59      (![X34 : $i, X35 : $i]:
% 1.37/1.59         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 1.37/1.59          | ~ (v1_relat_1 @ X35))),
% 1.37/1.59      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.37/1.59  thf('26', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.37/1.59            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['24', '25'])).
% 1.37/1.59  thf('27', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('28', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('29', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.37/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.37/1.59  thf(t90_relat_1, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( v1_relat_1 @ B ) =>
% 1.37/1.59       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 1.37/1.59         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.37/1.59  thf('30', plain,
% 1.37/1.59      (![X32 : $i, X33 : $i]:
% 1.37/1.59         (((k1_relat_1 @ (k7_relat_1 @ X32 @ X33))
% 1.37/1.59            = (k3_xboole_0 @ (k1_relat_1 @ X32) @ X33))
% 1.37/1.59          | ~ (v1_relat_1 @ X32))),
% 1.37/1.59      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.37/1.59  thf(commutativity_k3_xboole_0, axiom,
% 1.37/1.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.37/1.59  thf('31', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.37/1.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.37/1.59  thf(t17_xboole_1, axiom,
% 1.37/1.59    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.37/1.59  thf('32', plain,
% 1.37/1.59      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 1.37/1.59      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.37/1.59  thf('33', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.37/1.59      inference('sup+', [status(thm)], ['31', '32'])).
% 1.37/1.59  thf('34', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 1.37/1.59          | ~ (v1_relat_1 @ X1))),
% 1.37/1.59      inference('sup+', [status(thm)], ['30', '33'])).
% 1.37/1.59  thf('35', plain,
% 1.37/1.59      (![X29 : $i, X30 : $i]:
% 1.37/1.59         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 1.37/1.59          | ((k5_relat_1 @ (k6_relat_1 @ X30) @ X29) = (X29))
% 1.37/1.59          | ~ (v1_relat_1 @ X29))),
% 1.37/1.59      inference('cnf', [status(esa)], [t77_relat_1])).
% 1.37/1.59  thf('36', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (~ (v1_relat_1 @ X1)
% 1.37/1.59          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.37/1.59          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k7_relat_1 @ X1 @ X0))
% 1.37/1.59              = (k7_relat_1 @ X1 @ X0)))),
% 1.37/1.59      inference('sup-', [status(thm)], ['34', '35'])).
% 1.37/1.59  thf('37', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.37/1.59          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.37/1.59              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.37/1.59              = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.37/1.59      inference('sup-', [status(thm)], ['29', '36'])).
% 1.37/1.59  thf('38', plain,
% 1.37/1.59      (![X18 : $i, X19 : $i]:
% 1.37/1.59         (((k8_relat_1 @ X19 @ X18) = (k5_relat_1 @ X18 @ (k6_relat_1 @ X19)))
% 1.37/1.59          | ~ (v1_relat_1 @ X18))),
% 1.37/1.59      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.37/1.59  thf(t76_relat_1, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( v1_relat_1 @ B ) =>
% 1.37/1.59       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 1.37/1.59         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 1.37/1.59  thf('39', plain,
% 1.37/1.59      (![X27 : $i, X28 : $i]:
% 1.37/1.59         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X28) @ X27) @ X27)
% 1.37/1.59          | ~ (v1_relat_1 @ X27))),
% 1.37/1.59      inference('cnf', [status(esa)], [t76_relat_1])).
% 1.37/1.59  thf('40', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 1.37/1.59           (k6_relat_1 @ X1))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['38', '39'])).
% 1.37/1.59  thf('41', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('42', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('43', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X1))),
% 1.37/1.59      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.37/1.59  thf('44', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 1.37/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.37/1.59  thf(t125_relat_1, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( v1_relat_1 @ B ) =>
% 1.37/1.59       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.37/1.59         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 1.37/1.59  thf('45', plain,
% 1.37/1.59      (![X20 : $i, X21 : $i]:
% 1.37/1.59         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 1.37/1.59          | ((k8_relat_1 @ X21 @ X20) = (X20))
% 1.37/1.59          | ~ (v1_relat_1 @ X20))),
% 1.37/1.59      inference('cnf', [status(esa)], [t125_relat_1])).
% 1.37/1.59  thf('46', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (~ (r1_tarski @ X0 @ X1)
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.37/1.59          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('sup-', [status(thm)], ['44', '45'])).
% 1.37/1.59  thf('47', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('48', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (~ (r1_tarski @ X0 @ X1)
% 1.37/1.59          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('demod', [status(thm)], ['46', '47'])).
% 1.37/1.59  thf('49', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k8_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.37/1.59           (k6_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))
% 1.37/1.59           = (k6_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 1.37/1.59      inference('sup-', [status(thm)], ['43', '48'])).
% 1.37/1.59  thf('50', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 1.37/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.37/1.59  thf('51', plain,
% 1.37/1.59      (![X32 : $i, X33 : $i]:
% 1.37/1.59         (((k1_relat_1 @ (k7_relat_1 @ X32 @ X33))
% 1.37/1.59            = (k3_xboole_0 @ (k1_relat_1 @ X32) @ X33))
% 1.37/1.59          | ~ (v1_relat_1 @ X32))),
% 1.37/1.59      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.37/1.59  thf('52', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.37/1.59            = (k3_xboole_0 @ X0 @ X1))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['50', '51'])).
% 1.37/1.59  thf('53', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('54', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.37/1.59           = (k3_xboole_0 @ X0 @ X1))),
% 1.37/1.59      inference('demod', [status(thm)], ['52', '53'])).
% 1.37/1.59  thf('55', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.37/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.37/1.59  thf('56', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.37/1.59           = (k3_xboole_0 @ X0 @ X1))),
% 1.37/1.59      inference('demod', [status(thm)], ['54', '55'])).
% 1.37/1.59  thf('57', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k1_relat_1 @ (k6_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 1.37/1.59           = (k3_xboole_0 @ (k6_relat_1 @ X1) @ 
% 1.37/1.59              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 1.37/1.59      inference('sup+', [status(thm)], ['49', '56'])).
% 1.37/1.59  thf('58', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 1.37/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.37/1.59  thf('59', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 1.37/1.59           = (k3_xboole_0 @ (k6_relat_1 @ X1) @ 
% 1.37/1.59              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 1.37/1.59      inference('demod', [status(thm)], ['57', '58'])).
% 1.37/1.59  thf(fc1_relat_1, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.37/1.59  thf('60', plain,
% 1.37/1.59      (![X16 : $i, X17 : $i]:
% 1.37/1.59         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc1_relat_1])).
% 1.37/1.59  thf('61', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['59', '60'])).
% 1.37/1.59  thf('62', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('63', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('demod', [status(thm)], ['61', '62'])).
% 1.37/1.59  thf('64', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.37/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.37/1.59  thf('65', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.37/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.37/1.59  thf('66', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('67', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.37/1.59           (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.37/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('demod', [status(thm)], ['37', '63', '64', '65', '66'])).
% 1.37/1.59  thf('68', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 1.37/1.59           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['23', '67'])).
% 1.37/1.59  thf('69', plain,
% 1.37/1.59      (![X18 : $i, X19 : $i]:
% 1.37/1.59         (((k8_relat_1 @ X19 @ X18) = (k5_relat_1 @ X18 @ (k6_relat_1 @ X19)))
% 1.37/1.59          | ~ (v1_relat_1 @ X18))),
% 1.37/1.59      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.37/1.59  thf('70', plain,
% 1.37/1.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.37/1.59         (~ (v1_relat_1 @ X22)
% 1.37/1.59          | ((k5_relat_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 1.37/1.59              = (k5_relat_1 @ X23 @ (k5_relat_1 @ X22 @ X24)))
% 1.37/1.59          | ~ (v1_relat_1 @ X24)
% 1.37/1.59          | ~ (v1_relat_1 @ X23))),
% 1.37/1.59      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.37/1.59  thf('71', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.59         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 1.37/1.59            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 1.37/1.59          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.37/1.59          | ~ (v1_relat_1 @ X1)
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 1.37/1.59          | ~ (v1_relat_1 @ X0))),
% 1.37/1.59      inference('sup+', [status(thm)], ['69', '70'])).
% 1.37/1.59  thf('72', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('73', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.59         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 1.37/1.59            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 1.37/1.59          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.37/1.59          | ~ (v1_relat_1 @ X1)
% 1.37/1.59          | ~ (v1_relat_1 @ X0))),
% 1.37/1.59      inference('demod', [status(thm)], ['71', '72'])).
% 1.37/1.59  thf('74', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.59         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.37/1.59          | ((k8_relat_1 @ X2 @ 
% 1.37/1.59              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 1.37/1.59              = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.37/1.59                 (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2)))))),
% 1.37/1.59      inference('sup-', [status(thm)], ['68', '73'])).
% 1.37/1.59  thf('75', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('demod', [status(thm)], ['61', '62'])).
% 1.37/1.59  thf('76', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('77', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('78', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 1.37/1.59           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['23', '67'])).
% 1.37/1.59  thf('79', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 1.37/1.59           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['23', '67'])).
% 1.37/1.59  thf('80', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.59         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.37/1.59           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.37/1.59              (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))),
% 1.37/1.59      inference('demod', [status(thm)], ['74', '75', '76', '77', '78', '79'])).
% 1.37/1.59  thf('81', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (((k8_relat_1 @ X1 @ 
% 1.37/1.59            (k8_relat_1 @ X0 @ 
% 1.37/1.59             (k6_relat_1 @ (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))))
% 1.37/1.59            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.37/1.59          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 1.37/1.59      inference('sup+', [status(thm)], ['8', '80'])).
% 1.37/1.59  thf('82', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.37/1.59           = (k3_xboole_0 @ X0 @ X1))),
% 1.37/1.59      inference('demod', [status(thm)], ['54', '55'])).
% 1.37/1.59  thf('83', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.37/1.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.37/1.59  thf('84', plain,
% 1.37/1.59      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 1.37/1.59      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.37/1.59  thf('85', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (~ (r1_tarski @ X0 @ X1)
% 1.37/1.59          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('demod', [status(thm)], ['46', '47'])).
% 1.37/1.59  thf('86', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 1.37/1.59           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.37/1.59      inference('sup-', [status(thm)], ['84', '85'])).
% 1.37/1.59  thf('87', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 1.37/1.59           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['83', '86'])).
% 1.37/1.59  thf('88', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 1.37/1.59           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['83', '86'])).
% 1.37/1.59  thf('89', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('demod', [status(thm)], ['61', '62'])).
% 1.37/1.59  thf('90', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 1.37/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('demod', [status(thm)], ['81', '82', '87', '88', '89'])).
% 1.37/1.59  thf('91', plain,
% 1.37/1.59      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 1.37/1.59         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 1.37/1.59      inference('demod', [status(thm)], ['4', '90'])).
% 1.37/1.59  thf('92', plain, ($false), inference('simplify', [status(thm)], ['91'])).
% 1.37/1.59  
% 1.37/1.59  % SZS output end Refutation
% 1.37/1.59  
% 1.37/1.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
