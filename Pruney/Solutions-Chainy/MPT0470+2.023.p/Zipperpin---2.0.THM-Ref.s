%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QABqv5eUAu

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:29 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 744 expanded)
%              Number of leaves         :   24 ( 243 expanded)
%              Depth                    :   35
%              Number of atoms          :  800 (4120 expanded)
%              Number of equality atoms :   68 ( 312 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

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
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('5',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('10',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('11',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('16',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','13'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['3','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','13'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','31'])).

thf('33',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('34',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('36',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','13'])).

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

thf('42',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','30'])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['51'])).

thf('53',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','52'])).

thf('54',plain,(
    v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('56',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X14 ) @ ( k4_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','52'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','13'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('65',plain,(
    ! [X10: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','68'])).

thf('70',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','52'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('74',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A_1 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('82',plain,
    ( ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['74'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A_1 @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A_1 @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','13'])).

thf('87',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A_1 @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ~ ( v1_relat_1 @ sk_A_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','13'])).

thf('91',plain,
    ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['74'])).

thf('93',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A_1 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['76','93'])).

thf('95',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','13'])).

thf('98',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    $false ),
    inference(simplify,[status(thm)],['98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QABqv5eUAu
% 0.15/0.37  % Computer   : n002.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 17:20:52 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.83/1.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.83/1.05  % Solved by: fo/fo7.sh
% 0.83/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.05  % done 939 iterations in 0.564s
% 0.83/1.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.83/1.05  % SZS output start Refutation
% 0.83/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.05  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.83/1.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.83/1.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.83/1.05  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.83/1.05  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.83/1.05  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.83/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.05  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.83/1.05  thf(dt_k5_relat_1, axiom,
% 0.83/1.05    (![A:$i,B:$i]:
% 0.83/1.05     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.83/1.05       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.83/1.05  thf('0', plain,
% 0.83/1.05      (![X7 : $i, X8 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X7)
% 0.83/1.05          | ~ (v1_relat_1 @ X8)
% 0.83/1.05          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.83/1.05      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.83/1.05  thf(dt_k4_relat_1, axiom,
% 0.83/1.05    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.83/1.05  thf('1', plain,
% 0.83/1.05      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.83/1.05      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.83/1.05  thf(l13_xboole_0, axiom,
% 0.83/1.05    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.83/1.05  thf('2', plain,
% 0.83/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.05      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.05  thf(cc1_relat_1, axiom,
% 0.83/1.05    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.83/1.05  thf('3', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.83/1.05      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.83/1.05  thf('4', plain,
% 0.83/1.05      (![X7 : $i, X8 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X7)
% 0.83/1.05          | ~ (v1_relat_1 @ X8)
% 0.83/1.05          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.83/1.05      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.83/1.05  thf('5', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.83/1.05      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.83/1.05  thf(t60_relat_1, axiom,
% 0.83/1.05    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.83/1.05     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.83/1.05  thf('6', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.83/1.05      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.83/1.05  thf(t45_relat_1, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( v1_relat_1 @ A ) =>
% 0.83/1.05       ( ![B:$i]:
% 0.83/1.05         ( ( v1_relat_1 @ B ) =>
% 0.83/1.05           ( r1_tarski @
% 0.83/1.05             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.83/1.05  thf('7', plain,
% 0.83/1.05      (![X12 : $i, X13 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X12)
% 0.83/1.05          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X13 @ X12)) @ 
% 0.83/1.05             (k2_relat_1 @ X12))
% 0.83/1.05          | ~ (v1_relat_1 @ X13))),
% 0.83/1.05      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.83/1.05  thf('8', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.83/1.05           k1_xboole_0)
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['6', '7'])).
% 0.83/1.05  thf('9', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.83/1.05             k1_xboole_0))),
% 0.83/1.05      inference('sup-', [status(thm)], ['5', '8'])).
% 0.83/1.05  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.83/1.05  thf('10', plain, ((v1_xboole_0 @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.83/1.05  thf('11', plain, ((v1_xboole_0 @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.83/1.05  thf('12', plain,
% 0.83/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.05      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.05  thf('13', plain, (((sk_A) = (k1_xboole_0))),
% 0.83/1.05      inference('sup-', [status(thm)], ['11', '12'])).
% 0.83/1.05  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.05      inference('demod', [status(thm)], ['10', '13'])).
% 0.83/1.05  thf('15', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X0)
% 0.83/1.05          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.83/1.05             k1_xboole_0))),
% 0.83/1.05      inference('demod', [status(thm)], ['9', '14'])).
% 0.83/1.05  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.83/1.05  thf('16', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.83/1.05      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.83/1.05  thf(d10_xboole_0, axiom,
% 0.83/1.05    (![A:$i,B:$i]:
% 0.83/1.05     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.83/1.05  thf('17', plain,
% 0.83/1.05      (![X1 : $i, X3 : $i]:
% 0.83/1.05         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.83/1.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.05  thf('18', plain,
% 0.83/1.05      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['16', '17'])).
% 0.83/1.05  thf('19', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X0)
% 0.83/1.05          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['15', '18'])).
% 0.83/1.05  thf(fc9_relat_1, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.83/1.05       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.83/1.05  thf('20', plain,
% 0.83/1.05      (![X9 : $i]:
% 0.83/1.05         (~ (v1_xboole_0 @ (k2_relat_1 @ X9))
% 0.83/1.05          | ~ (v1_relat_1 @ X9)
% 0.83/1.05          | (v1_xboole_0 @ X9))),
% 0.83/1.05      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.83/1.05  thf('21', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.83/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['19', '20'])).
% 0.83/1.05  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.05      inference('demod', [status(thm)], ['10', '13'])).
% 0.83/1.05  thf('23', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X0)
% 0.83/1.05          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.83/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['21', '22'])).
% 0.83/1.05  thf('24', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ k1_xboole_0)
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.83/1.05          | ~ (v1_relat_1 @ X0))),
% 0.83/1.05      inference('sup-', [status(thm)], ['4', '23'])).
% 0.83/1.05  thf('25', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.83/1.05      inference('simplify', [status(thm)], ['24'])).
% 0.83/1.05  thf('26', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['3', '25'])).
% 0.83/1.05  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.05      inference('demod', [status(thm)], ['10', '13'])).
% 0.83/1.05  thf('28', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['26', '27'])).
% 0.83/1.05  thf('29', plain,
% 0.83/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.05      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.05  thf('30', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X0)
% 0.83/1.05          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['28', '29'])).
% 0.83/1.05  thf('31', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         (((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.83/1.05          | ~ (v1_xboole_0 @ X0)
% 0.83/1.05          | ~ (v1_relat_1 @ X1))),
% 0.83/1.05      inference('sup+', [status(thm)], ['2', '30'])).
% 0.83/1.05  thf('32', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X0)
% 0.83/1.05          | ~ (v1_xboole_0 @ X1)
% 0.83/1.05          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ X1) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['1', '31'])).
% 0.83/1.05  thf('33', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.83/1.05      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.83/1.05  thf('34', plain,
% 0.83/1.05      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.83/1.05      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.83/1.05  thf(t37_relat_1, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( v1_relat_1 @ A ) =>
% 0.83/1.05       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.83/1.05         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.83/1.05  thf('35', plain,
% 0.83/1.05      (![X11 : $i]:
% 0.83/1.05         (((k1_relat_1 @ X11) = (k2_relat_1 @ (k4_relat_1 @ X11)))
% 0.83/1.05          | ~ (v1_relat_1 @ X11))),
% 0.83/1.05      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.83/1.05  thf('36', plain,
% 0.83/1.05      (![X9 : $i]:
% 0.83/1.05         (~ (v1_xboole_0 @ (k2_relat_1 @ X9))
% 0.83/1.05          | ~ (v1_relat_1 @ X9)
% 0.83/1.05          | (v1_xboole_0 @ X9))),
% 0.83/1.05      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.83/1.05  thf('37', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.83/1.05          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['35', '36'])).
% 0.83/1.05  thf('38', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X0)
% 0.83/1.05          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['34', '37'])).
% 0.83/1.05  thf('39', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.83/1.05          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.83/1.05          | ~ (v1_relat_1 @ X0))),
% 0.83/1.05      inference('simplify', [status(thm)], ['38'])).
% 0.83/1.05  thf('40', plain,
% 0.83/1.05      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.83/1.05        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.83/1.05        | (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['33', '39'])).
% 0.83/1.05  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.05      inference('demod', [status(thm)], ['10', '13'])).
% 0.83/1.05  thf(t62_relat_1, conjecture,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( v1_relat_1 @ A ) =>
% 0.83/1.05       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.83/1.05         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.83/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.05    (~( ![A:$i]:
% 0.83/1.05        ( ( v1_relat_1 @ A ) =>
% 0.83/1.05          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.83/1.05            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.83/1.05    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.83/1.05  thf('42', plain, ((v1_relat_1 @ sk_A_1)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('43', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['26', '27'])).
% 0.83/1.05  thf('44', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.83/1.05      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.83/1.05  thf('45', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         (((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.83/1.05          | ~ (v1_xboole_0 @ X0)
% 0.83/1.05          | ~ (v1_relat_1 @ X1))),
% 0.83/1.05      inference('sup+', [status(thm)], ['2', '30'])).
% 0.83/1.05  thf('46', plain,
% 0.83/1.05      (![X7 : $i, X8 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X7)
% 0.83/1.05          | ~ (v1_relat_1 @ X8)
% 0.83/1.05          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.83/1.05      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.83/1.05  thf('47', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((v1_relat_1 @ k1_xboole_0)
% 0.83/1.05          | ~ (v1_relat_1 @ X1)
% 0.83/1.05          | ~ (v1_xboole_0 @ X0)
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | ~ (v1_relat_1 @ X1))),
% 0.83/1.05      inference('sup+', [status(thm)], ['45', '46'])).
% 0.83/1.05  thf('48', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X0)
% 0.83/1.05          | ~ (v1_xboole_0 @ X0)
% 0.83/1.05          | ~ (v1_relat_1 @ X1)
% 0.83/1.05          | (v1_relat_1 @ k1_xboole_0))),
% 0.83/1.05      inference('simplify', [status(thm)], ['47'])).
% 0.83/1.05  thf('49', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         (~ (v1_xboole_0 @ X0)
% 0.83/1.05          | (v1_relat_1 @ k1_xboole_0)
% 0.83/1.05          | ~ (v1_relat_1 @ X1)
% 0.83/1.05          | ~ (v1_xboole_0 @ X0))),
% 0.83/1.05      inference('sup-', [status(thm)], ['44', '48'])).
% 0.83/1.05  thf('50', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X1)
% 0.83/1.05          | (v1_relat_1 @ k1_xboole_0)
% 0.83/1.05          | ~ (v1_xboole_0 @ X0))),
% 0.83/1.05      inference('simplify', [status(thm)], ['49'])).
% 0.83/1.05  thf('51', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X0)
% 0.83/1.05          | (v1_relat_1 @ k1_xboole_0)
% 0.83/1.05          | ~ (v1_relat_1 @ X1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['43', '50'])).
% 0.83/1.05  thf('52', plain,
% 0.83/1.05      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.83/1.05      inference('condensation', [status(thm)], ['51'])).
% 0.83/1.05  thf('53', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.83/1.05      inference('sup-', [status(thm)], ['42', '52'])).
% 0.83/1.05  thf('54', plain, ((v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0))),
% 0.83/1.05      inference('demod', [status(thm)], ['40', '41', '53'])).
% 0.83/1.05  thf('55', plain,
% 0.83/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.05      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.05  thf('56', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.83/1.05      inference('sup-', [status(thm)], ['54', '55'])).
% 0.83/1.05  thf(t54_relat_1, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( v1_relat_1 @ A ) =>
% 0.83/1.05       ( ![B:$i]:
% 0.83/1.05         ( ( v1_relat_1 @ B ) =>
% 0.83/1.05           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.83/1.05             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.83/1.05  thf('57', plain,
% 0.83/1.05      (![X14 : $i, X15 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X14)
% 0.83/1.05          | ((k4_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 0.83/1.05              = (k5_relat_1 @ (k4_relat_1 @ X14) @ (k4_relat_1 @ X15)))
% 0.83/1.05          | ~ (v1_relat_1 @ X15))),
% 0.83/1.05      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.83/1.05  thf('58', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.83/1.05            = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0))
% 0.83/1.05          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.83/1.05          | ~ (v1_relat_1 @ X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['56', '57'])).
% 0.83/1.05  thf('59', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.83/1.05      inference('sup-', [status(thm)], ['42', '52'])).
% 0.83/1.05  thf('60', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.83/1.05            = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0))
% 0.83/1.05          | ~ (v1_relat_1 @ X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['58', '59'])).
% 0.83/1.05  thf('61', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.83/1.05          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | ~ (v1_relat_1 @ X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['32', '60'])).
% 0.83/1.05  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.05      inference('demod', [status(thm)], ['10', '13'])).
% 0.83/1.05  thf('63', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | ~ (v1_relat_1 @ X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['61', '62'])).
% 0.83/1.05  thf('64', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X0)
% 0.83/1.05          | ((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.83/1.05      inference('simplify', [status(thm)], ['63'])).
% 0.83/1.05  thf(involutiveness_k4_relat_1, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.83/1.05  thf('65', plain,
% 0.83/1.05      (![X10 : $i]:
% 0.83/1.05         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 0.83/1.05      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.83/1.05  thf('66', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['64', '65'])).
% 0.83/1.05  thf('67', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.83/1.05      inference('sup-', [status(thm)], ['54', '55'])).
% 0.83/1.05  thf('68', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['66', '67'])).
% 0.83/1.05  thf('69', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X0)
% 0.83/1.05          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['0', '68'])).
% 0.83/1.05  thf('70', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.83/1.05      inference('sup-', [status(thm)], ['42', '52'])).
% 0.83/1.05  thf('71', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X0)
% 0.83/1.05          | ~ (v1_relat_1 @ X0)
% 0.83/1.05          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['69', '70'])).
% 0.83/1.05  thf('72', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.83/1.05          | ~ (v1_relat_1 @ X0))),
% 0.83/1.05      inference('simplify', [status(thm)], ['71'])).
% 0.83/1.05  thf('73', plain,
% 0.83/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.05      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.05  thf('74', plain,
% 0.83/1.05      ((((k5_relat_1 @ k1_xboole_0 @ sk_A_1) != (k1_xboole_0))
% 0.83/1.05        | ((k5_relat_1 @ sk_A_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('75', plain,
% 0.83/1.05      ((((k5_relat_1 @ k1_xboole_0 @ sk_A_1) != (k1_xboole_0)))
% 0.83/1.05         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 0.83/1.05      inference('split', [status(esa)], ['74'])).
% 0.83/1.05  thf('76', plain,
% 0.83/1.05      ((![X0 : $i]:
% 0.83/1.05          (((k5_relat_1 @ X0 @ sk_A_1) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.83/1.05         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 0.83/1.05      inference('sup-', [status(thm)], ['73', '75'])).
% 0.83/1.05  thf('77', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['26', '27'])).
% 0.83/1.05  thf('78', plain,
% 0.83/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.05      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.05  thf('79', plain,
% 0.83/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.05      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.05  thf('80', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.83/1.05      inference('sup+', [status(thm)], ['78', '79'])).
% 0.83/1.05  thf('81', plain,
% 0.83/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.05      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.05  thf('82', plain,
% 0.83/1.05      ((((k5_relat_1 @ sk_A_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.83/1.05         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.83/1.05      inference('split', [status(esa)], ['74'])).
% 0.83/1.05  thf('83', plain,
% 0.83/1.05      ((![X0 : $i]:
% 0.83/1.05          (((k5_relat_1 @ sk_A_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.83/1.05         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.83/1.05      inference('sup-', [status(thm)], ['81', '82'])).
% 0.83/1.05  thf('84', plain,
% 0.83/1.05      ((![X0 : $i, X1 : $i]:
% 0.83/1.05          (((X0) != (k1_xboole_0))
% 0.83/1.05           | ~ (v1_xboole_0 @ X0)
% 0.83/1.05           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A_1 @ X1))
% 0.83/1.05           | ~ (v1_xboole_0 @ X1)))
% 0.83/1.05         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.83/1.05      inference('sup-', [status(thm)], ['80', '83'])).
% 0.83/1.05  thf('85', plain,
% 0.83/1.05      ((![X1 : $i]:
% 0.83/1.05          (~ (v1_xboole_0 @ X1)
% 0.83/1.05           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A_1 @ X1))
% 0.83/1.05           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.83/1.05         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.83/1.05      inference('simplify', [status(thm)], ['84'])).
% 0.83/1.05  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.05      inference('demod', [status(thm)], ['10', '13'])).
% 0.83/1.05  thf('87', plain,
% 0.83/1.05      ((![X1 : $i]:
% 0.83/1.05          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A_1 @ X1))))
% 0.83/1.05         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.83/1.05      inference('simplify_reflect+', [status(thm)], ['85', '86'])).
% 0.83/1.05  thf('88', plain,
% 0.83/1.05      (((~ (v1_relat_1 @ sk_A_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.83/1.05         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.83/1.05      inference('sup-', [status(thm)], ['77', '87'])).
% 0.83/1.05  thf('89', plain, ((v1_relat_1 @ sk_A_1)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.05      inference('demod', [status(thm)], ['10', '13'])).
% 0.83/1.05  thf('91', plain, ((((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.83/1.05  thf('92', plain,
% 0.83/1.05      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))) | 
% 0.83/1.05       ~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.83/1.05      inference('split', [status(esa)], ['74'])).
% 0.83/1.05  thf('93', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0)))),
% 0.83/1.05      inference('sat_resolution*', [status(thm)], ['91', '92'])).
% 0.83/1.05  thf('94', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (((k5_relat_1 @ X0 @ sk_A_1) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.05      inference('simpl_trail', [status(thm)], ['76', '93'])).
% 0.83/1.05  thf('95', plain,
% 0.83/1.05      ((((k1_xboole_0) != (k1_xboole_0))
% 0.83/1.05        | ~ (v1_relat_1 @ sk_A_1)
% 0.83/1.05        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.83/1.05      inference('sup-', [status(thm)], ['72', '94'])).
% 0.83/1.05  thf('96', plain, ((v1_relat_1 @ sk_A_1)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.05      inference('demod', [status(thm)], ['10', '13'])).
% 0.83/1.05  thf('98', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.83/1.05      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.83/1.05  thf('99', plain, ($false), inference('simplify', [status(thm)], ['98'])).
% 0.83/1.05  
% 0.83/1.05  % SZS output end Refutation
% 0.83/1.05  
% 0.90/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
