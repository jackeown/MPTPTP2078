%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3QyQcKEuc8

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:33 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 400 expanded)
%              Number of leaves         :   21 ( 132 expanded)
%              Depth                    :   29
%              Number of atoms          :  664 (2225 expanded)
%              Number of equality atoms :   47 ( 176 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('4',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('8',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('12',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('13',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','15'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','15'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['42'])).

thf('44',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','15'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','51'])).

thf('53',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','43'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('60',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A_1 @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','62'])).

thf('64',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A_1 @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','15'])).

thf('66',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A_1 @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('69',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','15'])).

thf('73',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_A_1 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('78',plain,(
    ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A_1 @ X1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['66','78'])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ sk_A_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','15'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['80','81','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3QyQcKEuc8
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 365 iterations in 0.226s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.49/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.49/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.68  thf(dt_k5_relat_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.49/0.68       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.49/0.68  thf('0', plain,
% 0.49/0.68      (![X6 : $i, X7 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X6)
% 0.49/0.68          | ~ (v1_relat_1 @ X7)
% 0.49/0.68          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.49/0.68  thf(t60_relat_1, axiom,
% 0.49/0.68    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.49/0.68     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.49/0.68  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.49/0.68  thf(t45_relat_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( v1_relat_1 @ B ) =>
% 0.49/0.68           ( r1_tarski @
% 0.49/0.68             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.49/0.68  thf('2', plain,
% 0.49/0.68      (![X12 : $i, X13 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X12)
% 0.49/0.68          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X13 @ X12)) @ 
% 0.49/0.68             (k2_relat_1 @ X12))
% 0.49/0.68          | ~ (v1_relat_1 @ X13))),
% 0.49/0.68      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.49/0.68  thf('3', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.49/0.68           k1_xboole_0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['1', '2'])).
% 0.49/0.68  thf(t62_relat_1, conjecture,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ A ) =>
% 0.49/0.68       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.49/0.68         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i]:
% 0.49/0.68        ( ( v1_relat_1 @ A ) =>
% 0.49/0.68          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.49/0.68            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.49/0.68  thf('4', plain, ((v1_relat_1 @ sk_A_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(cc1_relat_1, axiom,
% 0.49/0.68    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.49/0.68  thf('5', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.49/0.68      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.49/0.68  thf('6', plain,
% 0.49/0.68      (![X6 : $i, X7 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X6)
% 0.49/0.68          | ~ (v1_relat_1 @ X7)
% 0.49/0.68          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.49/0.68  thf('7', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.49/0.68      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.49/0.68  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.49/0.68  thf(t44_relat_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( v1_relat_1 @ B ) =>
% 0.49/0.68           ( r1_tarski @
% 0.49/0.68             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.49/0.68  thf('9', plain,
% 0.49/0.68      (![X10 : $i, X11 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X10)
% 0.49/0.68          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 0.49/0.68             (k1_relat_1 @ X11))
% 0.49/0.68          | ~ (v1_relat_1 @ X11))),
% 0.49/0.68      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.49/0.68  thf('10', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.49/0.68           k1_xboole_0)
% 0.49/0.68          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['8', '9'])).
% 0.49/0.68  thf('11', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.49/0.68             k1_xboole_0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['7', '10'])).
% 0.49/0.68  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.49/0.68  thf('12', plain, ((v1_xboole_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.49/0.68  thf('13', plain, ((v1_xboole_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.49/0.68  thf(l13_xboole_0, axiom,
% 0.49/0.68    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.49/0.68  thf('14', plain,
% 0.49/0.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.68  thf('15', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['13', '14'])).
% 0.49/0.68  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '15'])).
% 0.49/0.68  thf('17', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0)
% 0.49/0.68          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.49/0.68             k1_xboole_0))),
% 0.49/0.68      inference('demod', [status(thm)], ['11', '16'])).
% 0.49/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.49/0.68  thf('18', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.49/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.49/0.68  thf(d10_xboole_0, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.49/0.68  thf('19', plain,
% 0.49/0.68      (![X1 : $i, X3 : $i]:
% 0.49/0.68         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.49/0.68  thf('20', plain,
% 0.49/0.68      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.49/0.68  thf('21', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0)
% 0.49/0.68          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['17', '20'])).
% 0.49/0.68  thf(fc8_relat_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.49/0.68       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.49/0.68  thf('22', plain,
% 0.49/0.68      (![X8 : $i]:
% 0.49/0.68         (~ (v1_xboole_0 @ (k1_relat_1 @ X8))
% 0.49/0.68          | ~ (v1_relat_1 @ X8)
% 0.49/0.68          | (v1_xboole_0 @ X8))),
% 0.49/0.68      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.49/0.68  thf('23', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.49/0.68          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.49/0.68  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '15'])).
% 0.49/0.68  thf('25', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0)
% 0.49/0.68          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.49/0.68          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.49/0.68      inference('demod', [status(thm)], ['23', '24'])).
% 0.49/0.68  thf('26', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0)
% 0.49/0.68          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.68          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.49/0.68          | ~ (v1_relat_1 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['6', '25'])).
% 0.49/0.68  thf('27', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.49/0.68          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0))),
% 0.49/0.68      inference('simplify', [status(thm)], ['26'])).
% 0.49/0.68  thf('28', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['5', '27'])).
% 0.49/0.68  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '15'])).
% 0.49/0.68  thf('30', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.49/0.68      inference('demod', [status(thm)], ['28', '29'])).
% 0.49/0.68  thf('31', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.49/0.68      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.49/0.68  thf('32', plain,
% 0.49/0.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.68  thf('33', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.49/0.68      inference('demod', [status(thm)], ['28', '29'])).
% 0.49/0.68  thf('34', plain,
% 0.49/0.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.68  thf('35', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0)
% 0.49/0.68          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.68  thf('36', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.49/0.68          | ~ (v1_xboole_0 @ X0)
% 0.49/0.68          | ~ (v1_relat_1 @ X1))),
% 0.49/0.68      inference('sup+', [status(thm)], ['32', '35'])).
% 0.49/0.68  thf('37', plain,
% 0.49/0.68      (![X6 : $i, X7 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X6)
% 0.49/0.68          | ~ (v1_relat_1 @ X7)
% 0.49/0.68          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.49/0.68  thf('38', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((v1_relat_1 @ k1_xboole_0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | ~ (v1_xboole_0 @ X1)
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | ~ (v1_relat_1 @ X1))),
% 0.49/0.68      inference('sup+', [status(thm)], ['36', '37'])).
% 0.49/0.68  thf('39', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X1)
% 0.49/0.68          | ~ (v1_xboole_0 @ X1)
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | (v1_relat_1 @ k1_xboole_0))),
% 0.49/0.68      inference('simplify', [status(thm)], ['38'])).
% 0.49/0.68  thf('40', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (v1_xboole_0 @ X0)
% 0.49/0.68          | (v1_relat_1 @ k1_xboole_0)
% 0.49/0.68          | ~ (v1_relat_1 @ X1)
% 0.49/0.68          | ~ (v1_xboole_0 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['31', '39'])).
% 0.49/0.68  thf('41', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X1)
% 0.49/0.68          | (v1_relat_1 @ k1_xboole_0)
% 0.49/0.68          | ~ (v1_xboole_0 @ X0))),
% 0.49/0.68      inference('simplify', [status(thm)], ['40'])).
% 0.49/0.68  thf('42', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0)
% 0.49/0.68          | (v1_relat_1 @ k1_xboole_0)
% 0.49/0.68          | ~ (v1_relat_1 @ X1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['30', '41'])).
% 0.49/0.68  thf('43', plain,
% 0.49/0.68      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.49/0.68      inference('condensation', [status(thm)], ['42'])).
% 0.49/0.68  thf('44', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.49/0.68      inference('sup-', [status(thm)], ['4', '43'])).
% 0.49/0.68  thf('45', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.49/0.68           k1_xboole_0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0))),
% 0.49/0.68      inference('demod', [status(thm)], ['3', '44'])).
% 0.49/0.68  thf('46', plain,
% 0.49/0.68      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.49/0.68  thf('47', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0)
% 0.49/0.68          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['45', '46'])).
% 0.49/0.68  thf(fc9_relat_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.49/0.68       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.49/0.68  thf('48', plain,
% 0.49/0.68      (![X9 : $i]:
% 0.49/0.68         (~ (v1_xboole_0 @ (k2_relat_1 @ X9))
% 0.49/0.68          | ~ (v1_relat_1 @ X9)
% 0.49/0.68          | (v1_xboole_0 @ X9))),
% 0.49/0.68      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.49/0.68  thf('49', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.49/0.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['47', '48'])).
% 0.49/0.68  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '15'])).
% 0.49/0.68  thf('51', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0)
% 0.49/0.68          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.49/0.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.49/0.68      inference('demod', [status(thm)], ['49', '50'])).
% 0.49/0.68  thf('52', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.49/0.68          | ~ (v1_relat_1 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['0', '51'])).
% 0.49/0.68  thf('53', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.49/0.68      inference('sup-', [status(thm)], ['4', '43'])).
% 0.49/0.68  thf('54', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0)
% 0.49/0.68          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.49/0.68          | ~ (v1_relat_1 @ X0))),
% 0.49/0.68      inference('demod', [status(thm)], ['52', '53'])).
% 0.49/0.68  thf('55', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.49/0.68      inference('simplify', [status(thm)], ['54'])).
% 0.49/0.68  thf('56', plain,
% 0.49/0.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.68  thf('57', plain,
% 0.49/0.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.68  thf('58', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.68      inference('sup+', [status(thm)], ['56', '57'])).
% 0.49/0.68  thf('59', plain,
% 0.49/0.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.68  thf('60', plain,
% 0.49/0.68      ((((k5_relat_1 @ k1_xboole_0 @ sk_A_1) != (k1_xboole_0))
% 0.49/0.68        | ((k5_relat_1 @ sk_A_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('61', plain,
% 0.49/0.68      ((((k5_relat_1 @ sk_A_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.49/0.68         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.49/0.68      inference('split', [status(esa)], ['60'])).
% 0.49/0.68  thf('62', plain,
% 0.49/0.68      ((![X0 : $i]:
% 0.49/0.68          (((k5_relat_1 @ sk_A_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.49/0.68         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['59', '61'])).
% 0.49/0.68  thf('63', plain,
% 0.49/0.68      ((![X0 : $i, X1 : $i]:
% 0.49/0.68          (((X0) != (k1_xboole_0))
% 0.49/0.68           | ~ (v1_xboole_0 @ X0)
% 0.49/0.68           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A_1 @ X1))
% 0.49/0.68           | ~ (v1_xboole_0 @ X1)))
% 0.49/0.68         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['58', '62'])).
% 0.49/0.68  thf('64', plain,
% 0.49/0.68      ((![X1 : $i]:
% 0.49/0.68          (~ (v1_xboole_0 @ X1)
% 0.49/0.68           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A_1 @ X1))
% 0.49/0.68           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.49/0.68         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.49/0.68      inference('simplify', [status(thm)], ['63'])).
% 0.49/0.68  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '15'])).
% 0.49/0.68  thf('66', plain,
% 0.49/0.68      ((![X1 : $i]:
% 0.49/0.68          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A_1 @ X1))))
% 0.49/0.68         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.49/0.68      inference('simplify_reflect+', [status(thm)], ['64', '65'])).
% 0.49/0.68  thf('67', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.49/0.68      inference('demod', [status(thm)], ['28', '29'])).
% 0.49/0.68  thf('68', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.68      inference('sup+', [status(thm)], ['56', '57'])).
% 0.49/0.68  thf('69', plain,
% 0.49/0.68      ((((k5_relat_1 @ k1_xboole_0 @ sk_A_1) != (k1_xboole_0)))
% 0.49/0.68         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 0.49/0.68      inference('split', [status(esa)], ['60'])).
% 0.49/0.68  thf('70', plain,
% 0.49/0.68      ((![X0 : $i]:
% 0.49/0.68          (((X0) != (k1_xboole_0))
% 0.49/0.68           | ~ (v1_xboole_0 @ X0)
% 0.49/0.68           | ~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A_1))))
% 0.49/0.68         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['68', '69'])).
% 0.49/0.68  thf('71', plain,
% 0.49/0.68      (((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A_1))
% 0.49/0.68         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.49/0.68         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 0.49/0.68      inference('simplify', [status(thm)], ['70'])).
% 0.49/0.68  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '15'])).
% 0.49/0.68  thf('73', plain,
% 0.49/0.68      ((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A_1)))
% 0.49/0.68         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 0.49/0.68      inference('simplify_reflect+', [status(thm)], ['71', '72'])).
% 0.49/0.68  thf('74', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ sk_A_1))
% 0.49/0.68         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['67', '73'])).
% 0.49/0.68  thf('75', plain, ((v1_relat_1 @ sk_A_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('76', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0)))),
% 0.49/0.68      inference('demod', [status(thm)], ['74', '75'])).
% 0.49/0.68  thf('77', plain,
% 0.49/0.68      (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.49/0.68       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0)))),
% 0.49/0.68      inference('split', [status(esa)], ['60'])).
% 0.49/0.68  thf('78', plain, (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.49/0.68      inference('sat_resolution*', [status(thm)], ['76', '77'])).
% 0.49/0.68  thf('79', plain,
% 0.49/0.68      (![X1 : $i]:
% 0.49/0.68         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A_1 @ X1)))),
% 0.49/0.68      inference('simpl_trail', [status(thm)], ['66', '78'])).
% 0.49/0.68  thf('80', plain, ((~ (v1_relat_1 @ sk_A_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['55', '79'])).
% 0.49/0.68  thf('81', plain, ((v1_relat_1 @ sk_A_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '15'])).
% 0.49/0.68  thf('83', plain, ($false),
% 0.49/0.68      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.49/0.68  
% 0.49/0.68  % SZS output end Refutation
% 0.49/0.68  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
