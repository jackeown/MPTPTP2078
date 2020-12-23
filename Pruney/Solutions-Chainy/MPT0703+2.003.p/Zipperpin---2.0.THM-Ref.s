%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VelUvNqMv0

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:49 EST 2020

% Result     : Theorem 29.42s
% Output     : Refutation 29.42s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 760 expanded)
%              Number of leaves         :   23 ( 245 expanded)
%              Depth                    :   23
%              Number of atoms          : 1210 (7918 expanded)
%              Number of equality atoms :   88 ( 499 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t158_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X20: $i] :
      ( ( ( k9_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k9_relat_1 @ X25 @ ( k10_relat_1 @ X25 @ X24 ) )
        = ( k3_xboole_0 @ X24 @ ( k9_relat_1 @ X25 @ ( k1_relat_1 @ X25 ) ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X20: $i] :
      ( ( ( k9_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k9_relat_1 @ X25 @ ( k10_relat_1 @ X25 @ X24 ) )
        = ( k3_xboole_0 @ X24 @ ( k9_relat_1 @ X25 @ ( k1_relat_1 @ X25 ) ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['4','20'])).

thf('22',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k9_relat_1 @ X25 @ ( k10_relat_1 @ X25 @ X24 ) )
        = ( k3_xboole_0 @ X24 @ ( k9_relat_1 @ X25 @ ( k1_relat_1 @ X25 ) ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('25',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) )
      = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_C ) ) ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_C ) ) ) @ ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) )
      = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['23','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('42',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['39','46','47','48','49','50'])).

thf('52',plain,(
    ! [X20: $i] :
      ( ( ( k9_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t154_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('53',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X21 @ X22 ) @ ( k9_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t154_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['51','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['39','46','47','48','49','50'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('64',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k9_relat_1 @ X25 @ ( k10_relat_1 @ X25 @ X24 ) )
        = ( k3_xboole_0 @ X24 @ ( k9_relat_1 @ X25 @ ( k1_relat_1 @ X25 ) ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('73',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('75',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_B ) @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X21 @ X22 ) @ ( k9_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t154_relat_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_B ) ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) ) @ ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['70','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('80',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('82',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('83',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('84',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('89',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('96',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['94','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_A )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','80','81','82','87','88','91','104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('108',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('112',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['0','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VelUvNqMv0
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 29.42/29.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 29.42/29.61  % Solved by: fo/fo7.sh
% 29.42/29.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.42/29.61  % done 9113 iterations in 29.153s
% 29.42/29.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 29.42/29.61  % SZS output start Refutation
% 29.42/29.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 29.42/29.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 29.42/29.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 29.42/29.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 29.42/29.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 29.42/29.61  thf(sk_A_type, type, sk_A: $i).
% 29.42/29.61  thf(sk_B_type, type, sk_B: $i).
% 29.42/29.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 29.42/29.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 29.42/29.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 29.42/29.61  thf(sk_C_type, type, sk_C: $i).
% 29.42/29.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 29.42/29.61  thf(t158_funct_1, conjecture,
% 29.42/29.61    (![A:$i,B:$i,C:$i]:
% 29.42/29.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 29.42/29.61       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 29.42/29.61           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 29.42/29.61         ( r1_tarski @ A @ B ) ) ))).
% 29.42/29.61  thf(zf_stmt_0, negated_conjecture,
% 29.42/29.61    (~( ![A:$i,B:$i,C:$i]:
% 29.42/29.61        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 29.42/29.61          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 29.42/29.61              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 29.42/29.61            ( r1_tarski @ A @ B ) ) ) )),
% 29.42/29.61    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 29.42/29.61  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 29.42/29.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.42/29.61  thf(d10_xboole_0, axiom,
% 29.42/29.61    (![A:$i,B:$i]:
% 29.42/29.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 29.42/29.61  thf('1', plain,
% 29.42/29.61      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 29.42/29.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 29.42/29.61  thf('2', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 29.42/29.61      inference('simplify', [status(thm)], ['1'])).
% 29.42/29.61  thf(t28_xboole_1, axiom,
% 29.42/29.61    (![A:$i,B:$i]:
% 29.42/29.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 29.42/29.61  thf('3', plain,
% 29.42/29.61      (![X15 : $i, X16 : $i]:
% 29.42/29.61         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 29.42/29.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 29.42/29.61  thf('4', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 29.42/29.61      inference('sup-', [status(thm)], ['2', '3'])).
% 29.42/29.61  thf(t146_relat_1, axiom,
% 29.42/29.61    (![A:$i]:
% 29.42/29.61     ( ( v1_relat_1 @ A ) =>
% 29.42/29.61       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 29.42/29.61  thf('5', plain,
% 29.42/29.61      (![X20 : $i]:
% 29.42/29.61         (((k9_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (k2_relat_1 @ X20))
% 29.42/29.61          | ~ (v1_relat_1 @ X20))),
% 29.42/29.61      inference('cnf', [status(esa)], [t146_relat_1])).
% 29.42/29.61  thf(t148_funct_1, axiom,
% 29.42/29.61    (![A:$i,B:$i]:
% 29.42/29.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 29.42/29.61       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 29.42/29.61         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 29.42/29.61  thf('6', plain,
% 29.42/29.61      (![X24 : $i, X25 : $i]:
% 29.42/29.61         (((k9_relat_1 @ X25 @ (k10_relat_1 @ X25 @ X24))
% 29.42/29.61            = (k3_xboole_0 @ X24 @ (k9_relat_1 @ X25 @ (k1_relat_1 @ X25))))
% 29.42/29.61          | ~ (v1_funct_1 @ X25)
% 29.42/29.61          | ~ (v1_relat_1 @ X25))),
% 29.42/29.61      inference('cnf', [status(esa)], [t148_funct_1])).
% 29.42/29.61  thf('7', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 29.42/29.61            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 29.42/29.61          | ~ (v1_relat_1 @ X0)
% 29.42/29.61          | ~ (v1_relat_1 @ X0)
% 29.42/29.61          | ~ (v1_funct_1 @ X0))),
% 29.42/29.61      inference('sup+', [status(thm)], ['5', '6'])).
% 29.42/29.61  thf('8', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         (~ (v1_funct_1 @ X0)
% 29.42/29.61          | ~ (v1_relat_1 @ X0)
% 29.42/29.61          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 29.42/29.61              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 29.42/29.61      inference('simplify', [status(thm)], ['7'])).
% 29.42/29.61  thf('9', plain,
% 29.42/29.61      (![X20 : $i]:
% 29.42/29.61         (((k9_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (k2_relat_1 @ X20))
% 29.42/29.61          | ~ (v1_relat_1 @ X20))),
% 29.42/29.61      inference('cnf', [status(esa)], [t146_relat_1])).
% 29.42/29.61  thf('10', plain,
% 29.42/29.61      (![X24 : $i, X25 : $i]:
% 29.42/29.61         (((k9_relat_1 @ X25 @ (k10_relat_1 @ X25 @ X24))
% 29.42/29.61            = (k3_xboole_0 @ X24 @ (k9_relat_1 @ X25 @ (k1_relat_1 @ X25))))
% 29.42/29.61          | ~ (v1_funct_1 @ X25)
% 29.42/29.61          | ~ (v1_relat_1 @ X25))),
% 29.42/29.61      inference('cnf', [status(esa)], [t148_funct_1])).
% 29.42/29.61  thf(commutativity_k3_xboole_0, axiom,
% 29.42/29.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 29.42/29.61  thf('11', plain,
% 29.42/29.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 29.42/29.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.42/29.61  thf(t17_xboole_1, axiom,
% 29.42/29.61    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 29.42/29.61  thf('12', plain,
% 29.42/29.61      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 29.42/29.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 29.42/29.61  thf('13', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 29.42/29.61      inference('sup+', [status(thm)], ['11', '12'])).
% 29.42/29.61  thf('14', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         ((r1_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ 
% 29.42/29.61           (k9_relat_1 @ X1 @ (k1_relat_1 @ X1)))
% 29.42/29.61          | ~ (v1_relat_1 @ X1)
% 29.42/29.61          | ~ (v1_funct_1 @ X1))),
% 29.42/29.61      inference('sup+', [status(thm)], ['10', '13'])).
% 29.42/29.61  thf('15', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         ((r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)) @ 
% 29.42/29.61           (k2_relat_1 @ X0))
% 29.42/29.61          | ~ (v1_relat_1 @ X0)
% 29.42/29.61          | ~ (v1_funct_1 @ X0)
% 29.42/29.61          | ~ (v1_relat_1 @ X0))),
% 29.42/29.61      inference('sup+', [status(thm)], ['9', '14'])).
% 29.42/29.61  thf('16', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         (~ (v1_funct_1 @ X0)
% 29.42/29.61          | ~ (v1_relat_1 @ X0)
% 29.42/29.61          | (r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)) @ 
% 29.42/29.61             (k2_relat_1 @ X0)))),
% 29.42/29.61      inference('simplify', [status(thm)], ['15'])).
% 29.42/29.61  thf('17', plain,
% 29.42/29.61      (![X5 : $i, X7 : $i]:
% 29.42/29.61         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 29.42/29.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 29.42/29.61  thf('18', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         (~ (v1_relat_1 @ X0)
% 29.42/29.61          | ~ (v1_funct_1 @ X0)
% 29.42/29.61          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 29.42/29.61               (k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)))
% 29.42/29.61          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))))),
% 29.42/29.61      inference('sup-', [status(thm)], ['16', '17'])).
% 29.42/29.61  thf('19', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         (~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 29.42/29.61             (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 29.42/29.61          | ~ (v1_relat_1 @ X0)
% 29.42/29.61          | ~ (v1_funct_1 @ X0)
% 29.42/29.61          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)))
% 29.42/29.61          | ~ (v1_funct_1 @ X0)
% 29.42/29.61          | ~ (v1_relat_1 @ X0))),
% 29.42/29.61      inference('sup-', [status(thm)], ['8', '18'])).
% 29.42/29.61  thf('20', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)))
% 29.42/29.61          | ~ (v1_funct_1 @ X0)
% 29.42/29.61          | ~ (v1_relat_1 @ X0)
% 29.42/29.61          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 29.42/29.61               (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 29.42/29.61      inference('simplify', [status(thm)], ['19'])).
% 29.42/29.61  thf('21', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 29.42/29.61          | ~ (v1_relat_1 @ X0)
% 29.42/29.61          | ~ (v1_funct_1 @ X0)
% 29.42/29.61          | ((k2_relat_1 @ X0)
% 29.42/29.61              = (k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))))),
% 29.42/29.61      inference('sup-', [status(thm)], ['4', '20'])).
% 29.42/29.61  thf('22', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 29.42/29.61      inference('simplify', [status(thm)], ['1'])).
% 29.42/29.61  thf('23', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         (~ (v1_relat_1 @ X0)
% 29.42/29.61          | ~ (v1_funct_1 @ X0)
% 29.42/29.61          | ((k2_relat_1 @ X0)
% 29.42/29.61              = (k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))))),
% 29.42/29.61      inference('demod', [status(thm)], ['21', '22'])).
% 29.42/29.61  thf('24', plain,
% 29.42/29.61      (![X24 : $i, X25 : $i]:
% 29.42/29.61         (((k9_relat_1 @ X25 @ (k10_relat_1 @ X25 @ X24))
% 29.42/29.61            = (k3_xboole_0 @ X24 @ (k9_relat_1 @ X25 @ (k1_relat_1 @ X25))))
% 29.42/29.61          | ~ (v1_funct_1 @ X25)
% 29.42/29.61          | ~ (v1_relat_1 @ X25))),
% 29.42/29.61      inference('cnf', [status(esa)], [t148_funct_1])).
% 29.42/29.61  thf('25', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 29.42/29.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.42/29.61  thf('26', plain,
% 29.42/29.61      (![X15 : $i, X16 : $i]:
% 29.42/29.61         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 29.42/29.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 29.42/29.61  thf('27', plain, (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (sk_A))),
% 29.42/29.61      inference('sup-', [status(thm)], ['25', '26'])).
% 29.42/29.61  thf(t16_xboole_1, axiom,
% 29.42/29.61    (![A:$i,B:$i,C:$i]:
% 29.42/29.61     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 29.42/29.61       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 29.42/29.61  thf('28', plain,
% 29.42/29.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 29.42/29.61           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 29.42/29.61      inference('cnf', [status(esa)], [t16_xboole_1])).
% 29.42/29.61  thf('29', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ sk_A @ X0)
% 29.42/29.61           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0)))),
% 29.42/29.61      inference('sup+', [status(thm)], ['27', '28'])).
% 29.42/29.61  thf('30', plain,
% 29.42/29.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 29.42/29.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.42/29.61  thf(t22_xboole_1, axiom,
% 29.42/29.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 29.42/29.61  thf('31', plain,
% 29.42/29.61      (![X13 : $i, X14 : $i]:
% 29.42/29.61         ((k2_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)) = (X13))),
% 29.42/29.61      inference('cnf', [status(esa)], [t22_xboole_1])).
% 29.42/29.61  thf('32', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 29.42/29.61      inference('sup+', [status(thm)], ['30', '31'])).
% 29.42/29.61  thf('33', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         ((k2_xboole_0 @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0) @ 
% 29.42/29.61           (k3_xboole_0 @ sk_A @ X0))
% 29.42/29.61           = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))),
% 29.42/29.61      inference('sup+', [status(thm)], ['29', '32'])).
% 29.42/29.61  thf(commutativity_k2_xboole_0, axiom,
% 29.42/29.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 29.42/29.61  thf('34', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.42/29.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.42/29.61  thf('35', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         ((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 29.42/29.61           (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))
% 29.42/29.61           = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))),
% 29.42/29.61      inference('demod', [status(thm)], ['33', '34'])).
% 29.42/29.61  thf('36', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         (((k2_xboole_0 @ 
% 29.42/29.61            (k3_xboole_0 @ sk_A @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) @ 
% 29.42/29.61            (k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_C))))
% 29.42/29.61            = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ 
% 29.42/29.61               (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 29.42/29.61          | ~ (v1_relat_1 @ X0)
% 29.42/29.61          | ~ (v1_funct_1 @ X0))),
% 29.42/29.61      inference('sup+', [status(thm)], ['24', '35'])).
% 29.42/29.61  thf('37', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.42/29.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.42/29.61  thf('38', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         (((k2_xboole_0 @ 
% 29.42/29.61            (k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_C))) @ 
% 29.42/29.61            (k3_xboole_0 @ sk_A @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 29.42/29.61            = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ 
% 29.42/29.61               (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 29.42/29.61          | ~ (v1_relat_1 @ X0)
% 29.42/29.61          | ~ (v1_funct_1 @ X0))),
% 29.42/29.61      inference('demod', [status(thm)], ['36', '37'])).
% 29.42/29.61  thf('39', plain,
% 29.42/29.61      ((((k2_xboole_0 @ (k2_relat_1 @ sk_C) @ 
% 29.42/29.61          (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))
% 29.42/29.61          = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ 
% 29.42/29.61             (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))
% 29.42/29.61        | ~ (v1_funct_1 @ sk_C)
% 29.42/29.61        | ~ (v1_relat_1 @ sk_C)
% 29.42/29.61        | ~ (v1_funct_1 @ sk_C)
% 29.42/29.61        | ~ (v1_relat_1 @ sk_C))),
% 29.42/29.61      inference('sup+', [status(thm)], ['23', '38'])).
% 29.42/29.61  thf('40', plain,
% 29.42/29.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 29.42/29.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.42/29.61  thf('41', plain, (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (sk_A))),
% 29.42/29.61      inference('sup-', [status(thm)], ['25', '26'])).
% 29.42/29.61  thf('42', plain,
% 29.42/29.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 29.42/29.61           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 29.42/29.61      inference('cnf', [status(esa)], [t16_xboole_1])).
% 29.42/29.61  thf('43', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 29.42/29.61      inference('sup+', [status(thm)], ['30', '31'])).
% 29.42/29.61  thf('44', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.42/29.61         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 29.42/29.61           = (X0))),
% 29.42/29.61      inference('sup+', [status(thm)], ['42', '43'])).
% 29.42/29.61  thf('45', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         ((k2_xboole_0 @ (k2_relat_1 @ sk_C) @ (k3_xboole_0 @ X0 @ sk_A))
% 29.42/29.61           = (k2_relat_1 @ sk_C))),
% 29.42/29.61      inference('sup+', [status(thm)], ['41', '44'])).
% 29.42/29.61  thf('46', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         ((k2_xboole_0 @ (k2_relat_1 @ sk_C) @ (k3_xboole_0 @ sk_A @ X0))
% 29.42/29.61           = (k2_relat_1 @ sk_C))),
% 29.42/29.61      inference('sup+', [status(thm)], ['40', '45'])).
% 29.42/29.61  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 29.42/29.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.42/29.61  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 29.42/29.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.42/29.61  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 29.42/29.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.42/29.61  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 29.42/29.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.42/29.61  thf('51', plain,
% 29.42/29.61      (((k2_relat_1 @ sk_C)
% 29.42/29.61         = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ 
% 29.42/29.61            (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 29.42/29.61      inference('demod', [status(thm)], ['39', '46', '47', '48', '49', '50'])).
% 29.42/29.61  thf('52', plain,
% 29.42/29.61      (![X20 : $i]:
% 29.42/29.61         (((k9_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (k2_relat_1 @ X20))
% 29.42/29.61          | ~ (v1_relat_1 @ X20))),
% 29.42/29.61      inference('cnf', [status(esa)], [t146_relat_1])).
% 29.42/29.61  thf(t154_relat_1, axiom,
% 29.42/29.61    (![A:$i,B:$i,C:$i]:
% 29.42/29.61     ( ( v1_relat_1 @ C ) =>
% 29.42/29.61       ( r1_tarski @
% 29.42/29.61         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 29.42/29.61         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 29.42/29.61  thf('53', plain,
% 29.42/29.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 29.42/29.61         ((r1_tarski @ (k9_relat_1 @ X21 @ (k3_xboole_0 @ X22 @ X23)) @ 
% 29.42/29.61           (k3_xboole_0 @ (k9_relat_1 @ X21 @ X22) @ (k9_relat_1 @ X21 @ X23)))
% 29.42/29.61          | ~ (v1_relat_1 @ X21))),
% 29.42/29.61      inference('cnf', [status(esa)], [t154_relat_1])).
% 29.42/29.61  thf('54', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         ((r1_tarski @ 
% 29.42/29.61           (k9_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)) @ 
% 29.42/29.61           (k3_xboole_0 @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1)))
% 29.42/29.61          | ~ (v1_relat_1 @ X0)
% 29.42/29.61          | ~ (v1_relat_1 @ X0))),
% 29.42/29.61      inference('sup+', [status(thm)], ['52', '53'])).
% 29.42/29.61  thf('55', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         (~ (v1_relat_1 @ X0)
% 29.42/29.61          | (r1_tarski @ 
% 29.42/29.61             (k9_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)) @ 
% 29.42/29.61             (k3_xboole_0 @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))))),
% 29.42/29.61      inference('simplify', [status(thm)], ['54'])).
% 29.42/29.61  thf('56', plain,
% 29.42/29.61      (((r1_tarski @ 
% 29.42/29.61         (k9_relat_1 @ sk_C @ 
% 29.42/29.61          (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))) @ 
% 29.42/29.61         (k2_relat_1 @ sk_C))
% 29.42/29.61        | ~ (v1_relat_1 @ sk_C))),
% 29.42/29.61      inference('sup+', [status(thm)], ['51', '55'])).
% 29.42/29.61  thf('57', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 29.42/29.61      inference('sup-', [status(thm)], ['2', '3'])).
% 29.42/29.61  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 29.42/29.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.42/29.61  thf('59', plain,
% 29.42/29.61      ((r1_tarski @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) @ 
% 29.42/29.61        (k2_relat_1 @ sk_C))),
% 29.42/29.61      inference('demod', [status(thm)], ['56', '57', '58'])).
% 29.42/29.61  thf('60', plain,
% 29.42/29.61      (![X5 : $i, X7 : $i]:
% 29.42/29.61         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 29.42/29.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 29.42/29.61  thf('61', plain,
% 29.42/29.61      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 29.42/29.61           (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 29.42/29.61        | ((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 29.42/29.61      inference('sup-', [status(thm)], ['59', '60'])).
% 29.42/29.61  thf('62', plain,
% 29.42/29.61      (((k2_relat_1 @ sk_C)
% 29.42/29.61         = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ 
% 29.42/29.61            (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 29.42/29.61      inference('demod', [status(thm)], ['39', '46', '47', '48', '49', '50'])).
% 29.42/29.61  thf('63', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 29.42/29.61      inference('sup+', [status(thm)], ['11', '12'])).
% 29.42/29.61  thf('64', plain,
% 29.42/29.61      ((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 29.42/29.61        (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 29.42/29.61      inference('sup+', [status(thm)], ['62', '63'])).
% 29.42/29.61  thf('65', plain,
% 29.42/29.61      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 29.42/29.61      inference('demod', [status(thm)], ['61', '64'])).
% 29.42/29.61  thf('66', plain,
% 29.42/29.61      (![X24 : $i, X25 : $i]:
% 29.42/29.61         (((k9_relat_1 @ X25 @ (k10_relat_1 @ X25 @ X24))
% 29.42/29.61            = (k3_xboole_0 @ X24 @ (k9_relat_1 @ X25 @ (k1_relat_1 @ X25))))
% 29.42/29.61          | ~ (v1_funct_1 @ X25)
% 29.42/29.61          | ~ (v1_relat_1 @ X25))),
% 29.42/29.61      inference('cnf', [status(esa)], [t148_funct_1])).
% 29.42/29.61  thf('67', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0))
% 29.42/29.61            = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_C)))
% 29.42/29.61          | ~ (v1_relat_1 @ sk_C)
% 29.42/29.61          | ~ (v1_funct_1 @ sk_C))),
% 29.42/29.61      inference('sup+', [status(thm)], ['65', '66'])).
% 29.42/29.61  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 29.42/29.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.42/29.61  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 29.42/29.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.42/29.61  thf('70', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0))
% 29.42/29.61           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_C)))),
% 29.42/29.61      inference('demod', [status(thm)], ['67', '68', '69'])).
% 29.42/29.61  thf('71', plain,
% 29.42/29.61      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 29.42/29.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.42/29.61  thf('72', plain,
% 29.42/29.61      (![X15 : $i, X16 : $i]:
% 29.42/29.61         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 29.42/29.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 29.42/29.61  thf('73', plain,
% 29.42/29.61      (((k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 29.42/29.61         (k10_relat_1 @ sk_C @ sk_B)) = (k10_relat_1 @ sk_C @ sk_A))),
% 29.42/29.61      inference('sup-', [status(thm)], ['71', '72'])).
% 29.42/29.61  thf('74', plain,
% 29.42/29.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 29.42/29.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.42/29.61  thf('75', plain,
% 29.42/29.61      (((k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_B) @ 
% 29.42/29.61         (k10_relat_1 @ sk_C @ sk_A)) = (k10_relat_1 @ sk_C @ sk_A))),
% 29.42/29.61      inference('demod', [status(thm)], ['73', '74'])).
% 29.42/29.61  thf('76', plain,
% 29.42/29.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 29.42/29.61         ((r1_tarski @ (k9_relat_1 @ X21 @ (k3_xboole_0 @ X22 @ X23)) @ 
% 29.42/29.61           (k3_xboole_0 @ (k9_relat_1 @ X21 @ X22) @ (k9_relat_1 @ X21 @ X23)))
% 29.42/29.61          | ~ (v1_relat_1 @ X21))),
% 29.42/29.61      inference('cnf', [status(esa)], [t154_relat_1])).
% 29.42/29.61  thf('77', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         ((r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_A)) @ 
% 29.42/29.61           (k3_xboole_0 @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_B)) @ 
% 29.42/29.61            (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_A))))
% 29.42/29.61          | ~ (v1_relat_1 @ X0))),
% 29.42/29.61      inference('sup+', [status(thm)], ['75', '76'])).
% 29.42/29.61  thf('78', plain,
% 29.42/29.61      (((r1_tarski @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) @ 
% 29.42/29.61         (k3_xboole_0 @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) @ 
% 29.42/29.61          (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C))))
% 29.42/29.61        | ~ (v1_relat_1 @ sk_C))),
% 29.42/29.61      inference('sup+', [status(thm)], ['70', '77'])).
% 29.42/29.61  thf('79', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0))
% 29.42/29.61           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_C)))),
% 29.42/29.61      inference('demod', [status(thm)], ['67', '68', '69'])).
% 29.42/29.61  thf('80', plain, (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (sk_A))),
% 29.42/29.61      inference('sup-', [status(thm)], ['25', '26'])).
% 29.42/29.61  thf('81', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0))
% 29.42/29.61           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_C)))),
% 29.42/29.61      inference('demod', [status(thm)], ['67', '68', '69'])).
% 29.42/29.61  thf('82', plain, (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (sk_A))),
% 29.42/29.61      inference('sup-', [status(thm)], ['25', '26'])).
% 29.42/29.61  thf('83', plain,
% 29.42/29.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 29.42/29.61           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 29.42/29.61      inference('cnf', [status(esa)], [t16_xboole_1])).
% 29.42/29.61  thf('84', plain,
% 29.42/29.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 29.42/29.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.42/29.61  thf('85', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 29.42/29.61           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 29.42/29.61      inference('sup+', [status(thm)], ['83', '84'])).
% 29.42/29.61  thf('86', plain,
% 29.42/29.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 29.42/29.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.42/29.61  thf('87', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1)
% 29.42/29.61           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 29.42/29.61      inference('sup+', [status(thm)], ['85', '86'])).
% 29.42/29.61  thf('88', plain,
% 29.42/29.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 29.42/29.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.42/29.61  thf('89', plain,
% 29.42/29.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 29.42/29.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.42/29.61  thf('90', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 29.42/29.61           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 29.42/29.61      inference('sup+', [status(thm)], ['83', '84'])).
% 29.42/29.61  thf('91', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 29.42/29.61           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 29.42/29.61      inference('sup+', [status(thm)], ['89', '90'])).
% 29.42/29.61  thf('92', plain,
% 29.42/29.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 29.42/29.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.42/29.61  thf('93', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ sk_A @ X0)
% 29.42/29.61           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0)))),
% 29.42/29.61      inference('sup+', [status(thm)], ['27', '28'])).
% 29.42/29.61  thf('94', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ sk_A @ X0)
% 29.42/29.61           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_C))))),
% 29.42/29.61      inference('sup+', [status(thm)], ['92', '93'])).
% 29.42/29.61  thf('95', plain,
% 29.42/29.61      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 29.42/29.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 29.42/29.61  thf('96', plain,
% 29.42/29.61      (![X15 : $i, X16 : $i]:
% 29.42/29.61         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 29.42/29.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 29.42/29.61  thf('97', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 29.42/29.61           = (k3_xboole_0 @ X0 @ X1))),
% 29.42/29.61      inference('sup-', [status(thm)], ['95', '96'])).
% 29.42/29.61  thf('98', plain,
% 29.42/29.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 29.42/29.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.42/29.61  thf('99', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 29.42/29.61           = (k3_xboole_0 @ X0 @ X1))),
% 29.42/29.61      inference('demod', [status(thm)], ['97', '98'])).
% 29.42/29.61  thf('100', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0))
% 29.42/29.61           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_C))))),
% 29.42/29.61      inference('sup+', [status(thm)], ['94', '99'])).
% 29.42/29.61  thf('101', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 29.42/29.61      inference('sup-', [status(thm)], ['2', '3'])).
% 29.42/29.61  thf('102', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 29.42/29.61           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 29.42/29.61      inference('sup+', [status(thm)], ['83', '84'])).
% 29.42/29.61  thf('103', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ X1 @ X0)
% 29.42/29.61           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 29.42/29.61      inference('sup+', [status(thm)], ['101', '102'])).
% 29.42/29.61  thf('104', plain,
% 29.42/29.61      (![X0 : $i]:
% 29.42/29.61         ((k3_xboole_0 @ X0 @ sk_A)
% 29.42/29.61           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_C))))),
% 29.42/29.61      inference('demod', [status(thm)], ['100', '103'])).
% 29.42/29.61  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 29.42/29.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.42/29.61  thf('106', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))),
% 29.42/29.61      inference('demod', [status(thm)],
% 29.42/29.61                ['78', '79', '80', '81', '82', '87', '88', '91', '104', '105'])).
% 29.42/29.61  thf('107', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 29.42/29.61      inference('sup+', [status(thm)], ['11', '12'])).
% 29.42/29.61  thf('108', plain,
% 29.42/29.61      (![X5 : $i, X7 : $i]:
% 29.42/29.61         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 29.42/29.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 29.42/29.61  thf('109', plain,
% 29.42/29.61      (![X0 : $i, X1 : $i]:
% 29.42/29.61         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 29.42/29.61          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 29.42/29.61      inference('sup-', [status(thm)], ['107', '108'])).
% 29.42/29.61  thf('110', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 29.42/29.61      inference('sup-', [status(thm)], ['106', '109'])).
% 29.42/29.61  thf('111', plain,
% 29.42/29.61      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 29.42/29.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 29.42/29.61  thf('112', plain, ((r1_tarski @ sk_A @ sk_B)),
% 29.42/29.61      inference('sup+', [status(thm)], ['110', '111'])).
% 29.42/29.61  thf('113', plain, ($false), inference('demod', [status(thm)], ['0', '112'])).
% 29.42/29.61  
% 29.42/29.61  % SZS output end Refutation
% 29.42/29.61  
% 29.42/29.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
