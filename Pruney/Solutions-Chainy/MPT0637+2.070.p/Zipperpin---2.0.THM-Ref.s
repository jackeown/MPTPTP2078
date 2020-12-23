%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pu8hCBpEoQ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 179 expanded)
%              Number of leaves         :   25 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  770 (1493 expanded)
%              Number of equality atoms :   49 (  89 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k8_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X45: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X45 ) @ X45 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31
        = ( k7_relat_1 @ X31 @ X32 ) )
      | ~ ( v4_relat_1 @ X31 @ X32 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k8_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('11',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k7_relat_1 @ X43 @ X42 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('14',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','15'])).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k8_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('18',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X40 @ ( k6_relat_1 @ X41 ) ) @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( r1_tarski @ ( k2_relat_1 @ X34 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('27',plain,(
    ! [X38: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('28',plain,(
    ! [X38: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('29',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X27 )
      | ( ( k8_relat_1 @ X27 @ X26 )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) @ X21 )
        = ( k7_relat_1 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('37',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('41',plain,(
    ! [X38: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X23 @ X22 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('43',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k7_relat_1 @ X43 @ X42 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('44',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X40 @ ( k6_relat_1 @ X41 ) ) @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('47',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( r1_tarski @ ( k2_relat_1 @ X34 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('54',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k7_relat_1 @ X43 @ X42 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X38: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('64',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['52','62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['42','65'])).

thf('67',plain,(
    ! [X38: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('68',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X38: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('71',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X27 )
      | ( ( k8_relat_1 @ X27 @ X26 )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','75','76'])).

thf('78',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','77'])).

thf('79',plain,(
    $false ),
    inference(simplify,[status(thm)],['78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pu8hCBpEoQ
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 124 iterations in 0.089s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.55  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.55  thf(t123_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X24 : $i, X25 : $i]:
% 0.20/0.55         (((k8_relat_1 @ X25 @ X24) = (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)))
% 0.20/0.55          | ~ (v1_relat_1 @ X24))),
% 0.20/0.55      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.20/0.55  thf(t43_funct_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.20/0.55       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i]:
% 0.20/0.55        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.20/0.55          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.20/0.55         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.20/0.55          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.20/0.55        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf(fc24_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.20/0.55       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.20/0.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.55  thf('3', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.20/0.55         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf('5', plain, (![X45 : $i]: (v4_relat_1 @ (k6_relat_1 @ X45) @ X45)),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf(t209_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.55       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X31 : $i, X32 : $i]:
% 0.20/0.55         (((X31) = (k7_relat_1 @ X31 @ X32))
% 0.20/0.55          | ~ (v4_relat_1 @ X31 @ X32)
% 0.20/0.55          | ~ (v1_relat_1 @ X31))),
% 0.20/0.55      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.55          | ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf('8', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X0 : $i]: ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X24 : $i, X25 : $i]:
% 0.20/0.55         (((k8_relat_1 @ X25 @ X24) = (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)))
% 0.20/0.55          | ~ (v1_relat_1 @ X24))),
% 0.20/0.55      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.20/0.55  thf(t94_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X42 : $i, X43 : $i]:
% 0.20/0.55         (((k7_relat_1 @ X43 @ X42) = (k5_relat_1 @ (k6_relat_1 @ X42) @ X43))
% 0.20/0.55          | ~ (v1_relat_1 @ X43))),
% 0.20/0.55      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.55            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf('13', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('14', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.55           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X0 : $i]: ((k6_relat_1 @ X0) = (k8_relat_1 @ X0 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X24 : $i, X25 : $i]:
% 0.20/0.55         (((k8_relat_1 @ X25 @ X24) = (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)))
% 0.20/0.55          | ~ (v1_relat_1 @ X24))),
% 0.20/0.55      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.20/0.55  thf(t76_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.20/0.55         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X40 : $i, X41 : $i]:
% 0.20/0.55         ((r1_tarski @ (k5_relat_1 @ X40 @ (k6_relat_1 @ X41)) @ X40)
% 0.20/0.55          | ~ (v1_relat_1 @ X40))),
% 0.20/0.55      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0) | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r1_tarski @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['16', '20'])).
% 0.20/0.55  thf('22', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.55  thf(t25_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( v1_relat_1 @ B ) =>
% 0.20/0.55           ( ( r1_tarski @ A @ B ) =>
% 0.20/0.55             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.20/0.55               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X33 : $i, X34 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X33)
% 0.20/0.55          | (r1_tarski @ (k2_relat_1 @ X34) @ (k2_relat_1 @ X33))
% 0.20/0.55          | ~ (r1_tarski @ X34 @ X33)
% 0.20/0.55          | ~ (v1_relat_1 @ X34))),
% 0.20/0.55      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.55          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.20/0.55             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf(t71_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.55  thf('27', plain, (![X38 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.20/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.55  thf('28', plain, (![X38 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.20/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.55  thf('29', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('30', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.55      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.20/0.55  thf(t125_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.55         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X26 : $i, X27 : $i]:
% 0.20/0.55         (~ (r1_tarski @ (k2_relat_1 @ X26) @ X27)
% 0.20/0.55          | ((k8_relat_1 @ X27 @ X26) = (X26))
% 0.20/0.55          | ~ (v1_relat_1 @ X26))),
% 0.20/0.55      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.55           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.55  thf(t100_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ C ) =>
% 0.20/0.55       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.20/0.55         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.55         (((k7_relat_1 @ (k7_relat_1 @ X19 @ X20) @ X21)
% 0.20/0.55            = (k7_relat_1 @ X19 @ (k3_xboole_0 @ X20 @ X21)))
% 0.20/0.55          | ~ (v1_relat_1 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.20/0.55            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.55           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.55  thf('37', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.20/0.55           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 0.20/0.55      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.20/0.55            = (k8_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.20/0.55               (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['32', '38'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.55           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.55  thf('41', plain, (![X38 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.20/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.55  thf(t119_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.20/0.55         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (![X22 : $i, X23 : $i]:
% 0.20/0.55         (((k2_relat_1 @ (k8_relat_1 @ X23 @ X22))
% 0.20/0.55            = (k3_xboole_0 @ (k2_relat_1 @ X22) @ X23))
% 0.20/0.55          | ~ (v1_relat_1 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (![X42 : $i, X43 : $i]:
% 0.20/0.55         (((k7_relat_1 @ X43 @ X42) = (k5_relat_1 @ (k6_relat_1 @ X42) @ X43))
% 0.20/0.55          | ~ (v1_relat_1 @ X43))),
% 0.20/0.55      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (![X40 : $i, X41 : $i]:
% 0.20/0.55         ((r1_tarski @ (k5_relat_1 @ X40 @ (k6_relat_1 @ X41)) @ X40)
% 0.20/0.55          | ~ (v1_relat_1 @ X40))),
% 0.20/0.55      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.20/0.55           (k6_relat_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.55  thf('46', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('47', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.55           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (![X33 : $i, X34 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X33)
% 0.20/0.55          | (r1_tarski @ (k2_relat_1 @ X34) @ (k2_relat_1 @ X33))
% 0.20/0.55          | ~ (r1_tarski @ X34 @ X33)
% 0.20/0.55          | ~ (v1_relat_1 @ X34))),
% 0.20/0.55      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.20/0.55          | (r1_tarski @ 
% 0.20/0.55             (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.20/0.55             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.55           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      (![X42 : $i, X43 : $i]:
% 0.20/0.55         (((k7_relat_1 @ X43 @ X42) = (k5_relat_1 @ (k6_relat_1 @ X42) @ X43))
% 0.20/0.55          | ~ (v1_relat_1 @ X43))),
% 0.20/0.55      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.55  thf(dt_k5_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.20/0.55       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X16)
% 0.20/0.55          | ~ (v1_relat_1 @ X17)
% 0.20/0.55          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['54', '55'])).
% 0.20/0.55  thf('57', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ X1))),
% 0.20/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['53', '59'])).
% 0.20/0.55  thf('61', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.55  thf('63', plain, (![X38 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.20/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.55  thf('64', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X0)),
% 0.20/0.55      inference('demod', [status(thm)], ['52', '62', '63', '64'])).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ X0) @ 
% 0.20/0.55           X1)
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['42', '65'])).
% 0.20/0.55  thf('67', plain, (![X38 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.20/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.55  thf('68', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.20/0.55      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.20/0.55  thf('70', plain, (![X38 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.20/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      (![X26 : $i, X27 : $i]:
% 0.20/0.55         (~ (r1_tarski @ (k2_relat_1 @ X26) @ X27)
% 0.20/0.55          | ((k8_relat_1 @ X27 @ X26) = (X26))
% 0.20/0.55          | ~ (v1_relat_1 @ X26))),
% 0.20/0.55      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.55          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.55  thf('73', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.55          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['72', '73'])).
% 0.20/0.55  thf('75', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.20/0.55           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['69', '74'])).
% 0.20/0.55  thf('76', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.20/0.55           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['39', '40', '41', '75', '76'])).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.20/0.55         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['4', '77'])).
% 0.20/0.55  thf('79', plain, ($false), inference('simplify', [status(thm)], ['78'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
