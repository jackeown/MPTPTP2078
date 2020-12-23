%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8XJvGfwZrk

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 209 expanded)
%              Number of leaves         :   21 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  615 (1669 expanded)
%              Number of equality atoms :   56 ( 151 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k7_relat_1 @ X24 @ X23 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X23 ) @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ X14 @ X15 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k7_relat_1 @ X24 @ X23 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X23 ) @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k7_relat_1 @ X24 @ X23 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X23 ) @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X20: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X20 ) )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('9',plain,(
    ! [X20: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X20 ) )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X16 ) @ ( k4_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('25',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('27',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ( ( k7_relat_1 @ X25 @ X26 )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25','32','33'])).

thf('35',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','34'])).

thf('36',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ X14 @ X15 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('41',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('44',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('50',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25','32','33'])).

thf('54',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8XJvGfwZrk
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:53:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 62 iterations in 0.045s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(t94_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i]:
% 0.21/0.50         (((k7_relat_1 @ X24 @ X23) = (k5_relat_1 @ (k6_relat_1 @ X23) @ X24))
% 0.21/0.50          | ~ (v1_relat_1 @ X24))),
% 0.21/0.50      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.50  thf(t43_funct_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.50       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.50          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.21/0.50         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.21/0.50          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.50        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.50  thf('3', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.21/0.50         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf(t192_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( k7_relat_1 @ B @ A ) =
% 0.21/0.50         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i]:
% 0.21/0.50         (((k7_relat_1 @ X14 @ X15)
% 0.21/0.50            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15)))
% 0.21/0.50          | ~ (v1_relat_1 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i]:
% 0.21/0.50         (((k7_relat_1 @ X24 @ X23) = (k5_relat_1 @ (k6_relat_1 @ X23) @ X24))
% 0.21/0.50          | ~ (v1_relat_1 @ X24))),
% 0.21/0.50      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i]:
% 0.21/0.50         (((k7_relat_1 @ X24 @ X23) = (k5_relat_1 @ (k6_relat_1 @ X23) @ X24))
% 0.21/0.50          | ~ (v1_relat_1 @ X24))),
% 0.21/0.50      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.50  thf(t72_relat_1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X20 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X20)) = (k6_relat_1 @ X20))),
% 0.21/0.50      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X20 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X20)) = (k6_relat_1 @ X20))),
% 0.21/0.50      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.21/0.50  thf(t54_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( v1_relat_1 @ B ) =>
% 0.21/0.50           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.50             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X16)
% 0.21/0.50          | ((k4_relat_1 @ (k5_relat_1 @ X17 @ X16))
% 0.21/0.50              = (k5_relat_1 @ (k4_relat_1 @ X16) @ (k4_relat_1 @ X17)))
% 0.21/0.50          | ~ (v1_relat_1 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.50            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.21/0.50          | ~ (v1_relat_1 @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf('12', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.50            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.21/0.50          | ~ (v1_relat_1 @ X1))),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.21/0.50            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['8', '13'])).
% 0.21/0.50  thf('15', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.21/0.50           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.21/0.50            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['7', '16'])).
% 0.21/0.50  thf('18', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.21/0.50           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.21/0.50            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['6', '19'])).
% 0.21/0.50  thf('21', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.21/0.50           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.21/0.50            = (k7_relat_1 @ 
% 0.21/0.50               (k6_relat_1 @ 
% 0.21/0.50                (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 0.21/0.50               X1))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['5', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.21/0.50           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf(t71_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.50  thf('25', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf(t17_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.21/0.50      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.50  thf('27', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf(t97_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.21/0.50         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X25 : $i, X26 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 0.21/0.50          | ((k7_relat_1 @ X25 @ X26) = (X25))
% 0.21/0.50          | ~ (v1_relat_1 @ X25))),
% 0.21/0.50      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.50          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.50          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 0.21/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '31'])).
% 0.21/0.50  thf('33', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.21/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '24', '25', '32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (((k6_relat_1 @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.21/0.50         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '34'])).
% 0.21/0.50  thf('36', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i]:
% 0.21/0.50         (((k7_relat_1 @ X14 @ X15)
% 0.21/0.50            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15)))
% 0.21/0.50          | ~ (v1_relat_1 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.21/0.50            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.21/0.50           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf(t90_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.21/0.50         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i]:
% 0.21/0.50         (((k1_relat_1 @ (k7_relat_1 @ X21 @ X22))
% 0.21/0.50            = (k3_xboole_0 @ (k1_relat_1 @ X21) @ X22))
% 0.21/0.50          | ~ (v1_relat_1 @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.21/0.50            = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ 
% 0.21/0.50               (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('44', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.21/0.50           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i]:
% 0.21/0.50         (((k1_relat_1 @ (k7_relat_1 @ X21 @ X22))
% 0.21/0.50            = (k3_xboole_0 @ (k1_relat_1 @ X21) @ X22))
% 0.21/0.50          | ~ (v1_relat_1 @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.21/0.50           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)
% 0.21/0.50            = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['46', '47'])).
% 0.21/0.50  thf('49', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('50', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k3_xboole_0 @ X1 @ X0)
% 0.21/0.50           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.21/0.50           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['45', '51'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.21/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '24', '25', '32', '33'])).
% 0.21/0.50  thf('54', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.21/0.50         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '55'])).
% 0.21/0.50  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
