%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HLR7ClzCAQ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:29 EST 2020

% Result     : Theorem 19.48s
% Output     : Refutation 19.48s
% Verified   : 
% Statistics : Number of formulae       :  161 (1398 expanded)
%              Number of leaves         :   24 ( 461 expanded)
%              Depth                    :   38
%              Number of atoms          : 1017 (7778 expanded)
%              Number of equality atoms :   96 ( 774 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('5',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('6',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('8',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('12',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['5','8'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','27'])).

thf('29',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','36'])).

thf('38',plain,(
    ! [X10: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k1_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['5','8'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('49',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['47','52'])).

thf('54',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['5','8'])).

thf('56',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k1_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','56'])).

thf('58',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['5','8'])).

thf('60',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('61',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X14 ) @ ( k4_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('69',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('70',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('71',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['5','8'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('76',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('77',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('81',plain,(
    ! [X11: $i] :
      ( ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('82',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['5','8'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','88'])).

thf('90',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('94',plain,(
    ! [X10: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','96'])).

thf('98',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','102'])).

thf('104',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['5','8'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X10: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','110'])).

thf('112',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('116',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A_1 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('121',plain,
    ( ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['116'])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['5','8'])).

thf('126',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['116'])).

thf('129',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A_1 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['118','129'])).

thf('131',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['114','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['5','8'])).

thf('134',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    $false ),
    inference(simplify,[status(thm)],['134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HLR7ClzCAQ
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:04:15 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.36  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.37  % Running in FO mode
% 19.48/19.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 19.48/19.67  % Solved by: fo/fo7.sh
% 19.48/19.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.48/19.67  % done 15141 iterations in 19.193s
% 19.48/19.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 19.48/19.67  % SZS output start Refutation
% 19.48/19.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.48/19.67  thf(sk_A_type, type, sk_A: $i).
% 19.48/19.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 19.48/19.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 19.48/19.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 19.48/19.67  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 19.48/19.67  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 19.48/19.67  thf(sk_A_1_type, type, sk_A_1: $i).
% 19.48/19.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 19.48/19.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 19.48/19.67  thf(dt_k5_relat_1, axiom,
% 19.48/19.67    (![A:$i,B:$i]:
% 19.48/19.67     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 19.48/19.67       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 19.48/19.67  thf('0', plain,
% 19.48/19.67      (![X7 : $i, X8 : $i]:
% 19.48/19.67         (~ (v1_relat_1 @ X7)
% 19.48/19.67          | ~ (v1_relat_1 @ X8)
% 19.48/19.67          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 19.48/19.67      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 19.48/19.67  thf(t60_relat_1, axiom,
% 19.48/19.67    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 19.48/19.67     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 19.48/19.67  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.48/19.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 19.48/19.67  thf(l13_xboole_0, axiom,
% 19.48/19.67    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 19.48/19.67  thf('2', plain,
% 19.48/19.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.48/19.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 19.48/19.67  thf('3', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.48/19.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 19.48/19.67  thf('4', plain,
% 19.48/19.67      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.48/19.67      inference('sup+', [status(thm)], ['2', '3'])).
% 19.48/19.67  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 19.48/19.67  thf('5', plain, ((v1_xboole_0 @ sk_A)),
% 19.48/19.67      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 19.48/19.67  thf('6', plain, ((v1_xboole_0 @ sk_A)),
% 19.48/19.67      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 19.48/19.67  thf('7', plain,
% 19.48/19.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.48/19.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 19.48/19.67  thf('8', plain, (((sk_A) = (k1_xboole_0))),
% 19.48/19.67      inference('sup-', [status(thm)], ['6', '7'])).
% 19.48/19.67  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.48/19.67      inference('demod', [status(thm)], ['5', '8'])).
% 19.48/19.67  thf('10', plain,
% 19.48/19.67      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 19.48/19.67      inference('sup+', [status(thm)], ['4', '9'])).
% 19.48/19.67  thf(dt_k4_relat_1, axiom,
% 19.48/19.67    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 19.48/19.67  thf('11', plain,
% 19.48/19.67      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 19.48/19.67      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 19.48/19.67  thf('12', plain,
% 19.48/19.67      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 19.48/19.67      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 19.48/19.67  thf(involutiveness_k4_relat_1, axiom,
% 19.48/19.67    (![A:$i]:
% 19.48/19.67     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 19.48/19.67  thf('13', plain,
% 19.48/19.67      (![X10 : $i]:
% 19.48/19.67         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 19.48/19.67      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 19.48/19.67  thf(t37_relat_1, axiom,
% 19.48/19.67    (![A:$i]:
% 19.48/19.67     ( ( v1_relat_1 @ A ) =>
% 19.48/19.67       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 19.48/19.67         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 19.48/19.67  thf('14', plain,
% 19.48/19.67      (![X11 : $i]:
% 19.48/19.67         (((k1_relat_1 @ X11) = (k2_relat_1 @ (k4_relat_1 @ X11)))
% 19.48/19.67          | ~ (v1_relat_1 @ X11))),
% 19.48/19.67      inference('cnf', [status(esa)], [t37_relat_1])).
% 19.48/19.67  thf('15', plain,
% 19.48/19.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.48/19.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 19.48/19.67  thf('16', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.48/19.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 19.48/19.67  thf('17', plain,
% 19.48/19.67      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.48/19.67      inference('sup+', [status(thm)], ['15', '16'])).
% 19.48/19.67  thf('18', plain,
% 19.48/19.67      (![X0 : $i]:
% 19.48/19.67         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 19.48/19.67          | ~ (v1_relat_1 @ X0)
% 19.48/19.67          | ~ (v1_xboole_0 @ (k4_relat_1 @ X0)))),
% 19.48/19.67      inference('sup+', [status(thm)], ['14', '17'])).
% 19.48/19.67  thf('19', plain,
% 19.48/19.67      (![X0 : $i]:
% 19.48/19.67         (~ (v1_xboole_0 @ X0)
% 19.48/19.67          | ~ (v1_relat_1 @ X0)
% 19.48/19.67          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 19.48/19.67          | ((k1_relat_1 @ (k4_relat_1 @ X0)) = (k1_xboole_0)))),
% 19.48/19.67      inference('sup-', [status(thm)], ['13', '18'])).
% 19.48/19.67  thf('20', plain,
% 19.48/19.67      (![X0 : $i]:
% 19.48/19.67         (~ (v1_relat_1 @ X0)
% 19.48/19.67          | ((k1_relat_1 @ (k4_relat_1 @ X0)) = (k1_xboole_0))
% 19.48/19.67          | ~ (v1_relat_1 @ X0)
% 19.48/19.67          | ~ (v1_xboole_0 @ X0))),
% 19.48/19.67      inference('sup-', [status(thm)], ['12', '19'])).
% 19.48/19.67  thf('21', plain,
% 19.48/19.67      (![X0 : $i]:
% 19.48/19.67         (~ (v1_xboole_0 @ X0)
% 19.48/19.67          | ((k1_relat_1 @ (k4_relat_1 @ X0)) = (k1_xboole_0))
% 19.48/19.67          | ~ (v1_relat_1 @ X0))),
% 19.48/19.67      inference('simplify', [status(thm)], ['20'])).
% 19.48/19.67  thf(cc1_relat_1, axiom,
% 19.48/19.67    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 19.48/19.67  thf('22', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 19.48/19.67      inference('cnf', [status(esa)], [cc1_relat_1])).
% 19.48/19.67  thf('23', plain,
% 19.48/19.67      (![X0 : $i]:
% 19.48/19.67         (((k1_relat_1 @ (k4_relat_1 @ X0)) = (k1_xboole_0))
% 19.48/19.67          | ~ (v1_xboole_0 @ X0))),
% 19.48/19.67      inference('clc', [status(thm)], ['21', '22'])).
% 19.48/19.67  thf(fc8_relat_1, axiom,
% 19.48/19.67    (![A:$i]:
% 19.48/19.67     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 19.48/19.67       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 19.48/19.67  thf('24', plain,
% 19.48/19.67      (![X9 : $i]:
% 19.48/19.67         (~ (v1_xboole_0 @ (k1_relat_1 @ X9))
% 19.48/19.67          | ~ (v1_relat_1 @ X9)
% 19.48/19.67          | (v1_xboole_0 @ X9))),
% 19.48/19.67      inference('cnf', [status(esa)], [fc8_relat_1])).
% 19.48/19.67  thf('25', plain,
% 19.48/19.67      (![X0 : $i]:
% 19.48/19.67         (~ (v1_xboole_0 @ k1_xboole_0)
% 19.48/19.67          | ~ (v1_xboole_0 @ X0)
% 19.48/19.67          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 19.48/19.67          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 19.48/19.67      inference('sup-', [status(thm)], ['23', '24'])).
% 19.48/19.67  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.48/19.67      inference('demod', [status(thm)], ['5', '8'])).
% 19.48/19.67  thf('27', plain,
% 19.48/19.67      (![X0 : $i]:
% 19.48/19.67         (~ (v1_xboole_0 @ X0)
% 19.48/19.67          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 19.48/19.67          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 19.48/19.67      inference('demod', [status(thm)], ['25', '26'])).
% 19.48/19.67  thf('28', plain,
% 19.48/19.67      (![X0 : $i]:
% 19.48/19.67         (~ (v1_relat_1 @ X0)
% 19.48/19.67          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 19.48/19.67          | ~ (v1_xboole_0 @ X0))),
% 19.48/19.67      inference('sup-', [status(thm)], ['11', '27'])).
% 19.48/19.67  thf('29', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 19.48/19.67      inference('cnf', [status(esa)], [cc1_relat_1])).
% 19.48/19.67  thf('30', plain,
% 19.48/19.67      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k4_relat_1 @ X0)))),
% 19.48/19.67      inference('clc', [status(thm)], ['28', '29'])).
% 19.48/19.67  thf('31', plain,
% 19.48/19.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.48/19.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 19.48/19.67  thf('32', plain,
% 19.48/19.67      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 19.48/19.67      inference('sup-', [status(thm)], ['30', '31'])).
% 19.48/19.67  thf('33', plain,
% 19.48/19.67      (![X10 : $i]:
% 19.48/19.67         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 19.48/19.67      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 19.48/19.67  thf('34', plain,
% 19.48/19.67      (![X0 : $i]:
% 19.48/19.67         (((k4_relat_1 @ k1_xboole_0) = (X0))
% 19.48/19.67          | ~ (v1_xboole_0 @ X0)
% 19.48/19.67          | ~ (v1_relat_1 @ X0))),
% 19.48/19.67      inference('sup+', [status(thm)], ['32', '33'])).
% 19.48/19.67  thf('35', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 19.48/19.67      inference('cnf', [status(esa)], [cc1_relat_1])).
% 19.48/19.67  thf('36', plain,
% 19.48/19.67      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ k1_xboole_0) = (X0)))),
% 19.48/19.67      inference('clc', [status(thm)], ['34', '35'])).
% 19.48/19.67  thf('37', plain,
% 19.48/19.67      (![X0 : $i]:
% 19.48/19.67         (~ (v1_xboole_0 @ X0)
% 19.48/19.67          | ((k4_relat_1 @ k1_xboole_0) = (k1_relat_1 @ X0)))),
% 19.48/19.67      inference('sup-', [status(thm)], ['10', '36'])).
% 19.48/19.67  thf('38', plain,
% 19.48/19.67      (![X10 : $i]:
% 19.48/19.67         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 19.48/19.67      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 19.48/19.67  thf('39', plain,
% 19.48/19.67      (![X0 : $i]:
% 19.48/19.67         (((k4_relat_1 @ (k1_relat_1 @ X0)) = (k1_xboole_0))
% 19.48/19.67          | ~ (v1_xboole_0 @ X0)
% 19.48/19.67          | ~ (v1_relat_1 @ k1_xboole_0))),
% 19.48/19.67      inference('sup+', [status(thm)], ['37', '38'])).
% 19.48/19.67  thf('40', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.48/19.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 19.48/19.67  thf('41', plain,
% 19.48/19.67      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.48/19.67      inference('sup+', [status(thm)], ['15', '16'])).
% 19.48/19.67  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.48/19.67      inference('demod', [status(thm)], ['5', '8'])).
% 19.48/19.67  thf('43', plain,
% 19.48/19.67      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 19.48/19.67      inference('sup+', [status(thm)], ['41', '42'])).
% 19.48/19.67  thf('44', plain,
% 19.48/19.67      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ k1_xboole_0) = (X0)))),
% 19.48/19.67      inference('clc', [status(thm)], ['34', '35'])).
% 19.48/19.67  thf('45', plain,
% 19.48/19.67      (![X0 : $i]:
% 19.48/19.67         (~ (v1_xboole_0 @ X0)
% 19.48/19.67          | ((k4_relat_1 @ k1_xboole_0) = (k2_relat_1 @ X0)))),
% 19.48/19.67      inference('sup-', [status(thm)], ['43', '44'])).
% 19.48/19.67  thf('46', plain,
% 19.48/19.67      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 19.48/19.67      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 19.48/19.67  thf('47', plain,
% 19.48/19.67      (![X0 : $i]:
% 19.48/19.67         ((v1_relat_1 @ (k2_relat_1 @ X0))
% 19.48/19.67          | ~ (v1_xboole_0 @ X0)
% 19.48/19.67          | ~ (v1_relat_1 @ k1_xboole_0))),
% 19.48/19.67      inference('sup+', [status(thm)], ['45', '46'])).
% 19.48/19.67  thf('48', plain,
% 19.48/19.67      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 19.48/19.67      inference('sup-', [status(thm)], ['30', '31'])).
% 19.48/19.67  thf('49', plain,
% 19.48/19.67      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 19.48/19.67      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 19.48/19.67  thf('50', plain,
% 19.48/19.67      (![X0 : $i]:
% 19.48/19.67         ((v1_relat_1 @ k1_xboole_0)
% 19.48/19.67          | ~ (v1_xboole_0 @ X0)
% 19.48/19.67          | ~ (v1_relat_1 @ X0))),
% 19.48/19.67      inference('sup+', [status(thm)], ['48', '49'])).
% 19.48/19.67  thf('51', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 19.48/19.67      inference('cnf', [status(esa)], [cc1_relat_1])).
% 19.48/19.67  thf('52', plain,
% 19.48/19.67      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 19.48/19.67      inference('clc', [status(thm)], ['50', '51'])).
% 19.48/19.68  thf('53', plain,
% 19.48/19.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ (k2_relat_1 @ X0)))),
% 19.48/19.68      inference('clc', [status(thm)], ['47', '52'])).
% 19.48/19.68  thf('54', plain,
% 19.48/19.68      (((v1_relat_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 19.48/19.68      inference('sup+', [status(thm)], ['40', '53'])).
% 19.48/19.68  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.48/19.68      inference('demod', [status(thm)], ['5', '8'])).
% 19.48/19.68  thf('56', plain, ((v1_relat_1 @ k1_xboole_0)),
% 19.48/19.68      inference('demod', [status(thm)], ['54', '55'])).
% 19.48/19.68  thf('57', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (((k4_relat_1 @ (k1_relat_1 @ X0)) = (k1_xboole_0))
% 19.48/19.68          | ~ (v1_xboole_0 @ X0))),
% 19.48/19.68      inference('demod', [status(thm)], ['39', '56'])).
% 19.48/19.68  thf('58', plain,
% 19.48/19.68      ((((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 19.48/19.68        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 19.48/19.68      inference('sup+', [status(thm)], ['1', '57'])).
% 19.48/19.68  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.48/19.68      inference('demod', [status(thm)], ['5', '8'])).
% 19.48/19.68  thf('60', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.48/19.68      inference('demod', [status(thm)], ['58', '59'])).
% 19.48/19.68  thf(t54_relat_1, axiom,
% 19.48/19.68    (![A:$i]:
% 19.48/19.68     ( ( v1_relat_1 @ A ) =>
% 19.48/19.68       ( ![B:$i]:
% 19.48/19.68         ( ( v1_relat_1 @ B ) =>
% 19.48/19.68           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 19.48/19.68             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 19.48/19.68  thf('61', plain,
% 19.48/19.68      (![X14 : $i, X15 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X14)
% 19.48/19.68          | ((k4_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 19.48/19.68              = (k5_relat_1 @ (k4_relat_1 @ X14) @ (k4_relat_1 @ X15)))
% 19.48/19.68          | ~ (v1_relat_1 @ X15))),
% 19.48/19.68      inference('cnf', [status(esa)], [t54_relat_1])).
% 19.48/19.68  thf('62', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 19.48/19.68            = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0))
% 19.48/19.68          | ~ (v1_relat_1 @ k1_xboole_0)
% 19.48/19.68          | ~ (v1_relat_1 @ X0))),
% 19.48/19.68      inference('sup+', [status(thm)], ['60', '61'])).
% 19.48/19.68  thf('63', plain, ((v1_relat_1 @ k1_xboole_0)),
% 19.48/19.68      inference('demod', [status(thm)], ['54', '55'])).
% 19.48/19.68  thf('64', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 19.48/19.68            = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0))
% 19.48/19.68          | ~ (v1_relat_1 @ X0))),
% 19.48/19.68      inference('demod', [status(thm)], ['62', '63'])).
% 19.48/19.68  thf('65', plain,
% 19.48/19.68      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 19.48/19.68      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 19.48/19.68  thf('66', plain,
% 19.48/19.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.48/19.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 19.48/19.68  thf('67', plain,
% 19.48/19.68      (![X7 : $i, X8 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X7)
% 19.48/19.68          | ~ (v1_relat_1 @ X8)
% 19.48/19.68          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 19.48/19.68      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 19.48/19.68  thf('68', plain,
% 19.48/19.68      (![X7 : $i, X8 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X7)
% 19.48/19.68          | ~ (v1_relat_1 @ X8)
% 19.48/19.68          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 19.48/19.68      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 19.48/19.68  thf('69', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 19.48/19.68      inference('cnf', [status(esa)], [cc1_relat_1])).
% 19.48/19.68  thf('70', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.48/19.68      inference('cnf', [status(esa)], [t60_relat_1])).
% 19.48/19.68  thf(t45_relat_1, axiom,
% 19.48/19.68    (![A:$i]:
% 19.48/19.68     ( ( v1_relat_1 @ A ) =>
% 19.48/19.68       ( ![B:$i]:
% 19.48/19.68         ( ( v1_relat_1 @ B ) =>
% 19.48/19.68           ( r1_tarski @
% 19.48/19.68             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 19.48/19.68  thf('71', plain,
% 19.48/19.68      (![X12 : $i, X13 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X12)
% 19.48/19.68          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X13 @ X12)) @ 
% 19.48/19.68             (k2_relat_1 @ X12))
% 19.48/19.68          | ~ (v1_relat_1 @ X13))),
% 19.48/19.68      inference('cnf', [status(esa)], [t45_relat_1])).
% 19.48/19.68  thf('72', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 19.48/19.68           k1_xboole_0)
% 19.48/19.68          | ~ (v1_relat_1 @ X0)
% 19.48/19.68          | ~ (v1_relat_1 @ k1_xboole_0))),
% 19.48/19.68      inference('sup+', [status(thm)], ['70', '71'])).
% 19.48/19.68  thf('73', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_xboole_0 @ k1_xboole_0)
% 19.48/19.68          | ~ (v1_relat_1 @ X0)
% 19.48/19.68          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 19.48/19.68             k1_xboole_0))),
% 19.48/19.68      inference('sup-', [status(thm)], ['69', '72'])).
% 19.48/19.68  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.48/19.68      inference('demod', [status(thm)], ['5', '8'])).
% 19.48/19.68  thf('75', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X0)
% 19.48/19.68          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 19.48/19.68             k1_xboole_0))),
% 19.48/19.68      inference('demod', [status(thm)], ['73', '74'])).
% 19.48/19.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 19.48/19.68  thf('76', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 19.48/19.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 19.48/19.68  thf(d10_xboole_0, axiom,
% 19.48/19.68    (![A:$i,B:$i]:
% 19.48/19.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 19.48/19.68  thf('77', plain,
% 19.48/19.68      (![X1 : $i, X3 : $i]:
% 19.48/19.68         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 19.48/19.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.48/19.68  thf('78', plain,
% 19.48/19.68      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 19.48/19.68      inference('sup-', [status(thm)], ['76', '77'])).
% 19.48/19.68  thf('79', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X0)
% 19.48/19.68          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 19.48/19.68      inference('sup-', [status(thm)], ['75', '78'])).
% 19.48/19.68  thf('80', plain,
% 19.48/19.68      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 19.48/19.68      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 19.48/19.68  thf('81', plain,
% 19.48/19.68      (![X11 : $i]:
% 19.48/19.68         (((k2_relat_1 @ X11) = (k1_relat_1 @ (k4_relat_1 @ X11)))
% 19.48/19.68          | ~ (v1_relat_1 @ X11))),
% 19.48/19.68      inference('cnf', [status(esa)], [t37_relat_1])).
% 19.48/19.68  thf('82', plain,
% 19.48/19.68      (![X9 : $i]:
% 19.48/19.68         (~ (v1_xboole_0 @ (k1_relat_1 @ X9))
% 19.48/19.68          | ~ (v1_relat_1 @ X9)
% 19.48/19.68          | (v1_xboole_0 @ X9))),
% 19.48/19.68      inference('cnf', [status(esa)], [fc8_relat_1])).
% 19.48/19.68  thf('83', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 19.48/19.68          | ~ (v1_relat_1 @ X0)
% 19.48/19.68          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 19.48/19.68          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 19.48/19.68      inference('sup-', [status(thm)], ['81', '82'])).
% 19.48/19.68  thf('84', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X0)
% 19.48/19.68          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 19.48/19.68          | ~ (v1_relat_1 @ X0)
% 19.48/19.68          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 19.48/19.68      inference('sup-', [status(thm)], ['80', '83'])).
% 19.48/19.68  thf('85', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 19.48/19.68          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 19.48/19.68          | ~ (v1_relat_1 @ X0))),
% 19.48/19.68      inference('simplify', [status(thm)], ['84'])).
% 19.48/19.68  thf('86', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_xboole_0 @ k1_xboole_0)
% 19.48/19.68          | ~ (v1_relat_1 @ X0)
% 19.48/19.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 19.48/19.68          | (v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 19.48/19.68      inference('sup-', [status(thm)], ['79', '85'])).
% 19.48/19.68  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.48/19.68      inference('demod', [status(thm)], ['5', '8'])).
% 19.48/19.68  thf('88', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X0)
% 19.48/19.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 19.48/19.68          | (v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 19.48/19.68      inference('demod', [status(thm)], ['86', '87'])).
% 19.48/19.68  thf('89', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ k1_xboole_0)
% 19.48/19.68          | ~ (v1_relat_1 @ X0)
% 19.48/19.68          | (v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 19.48/19.68          | ~ (v1_relat_1 @ X0))),
% 19.48/19.68      inference('sup-', [status(thm)], ['68', '88'])).
% 19.48/19.68  thf('90', plain, ((v1_relat_1 @ k1_xboole_0)),
% 19.48/19.68      inference('demod', [status(thm)], ['54', '55'])).
% 19.48/19.68  thf('91', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X0)
% 19.48/19.68          | (v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 19.48/19.68          | ~ (v1_relat_1 @ X0))),
% 19.48/19.68      inference('demod', [status(thm)], ['89', '90'])).
% 19.48/19.68  thf('92', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         ((v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 19.48/19.68          | ~ (v1_relat_1 @ X0))),
% 19.48/19.68      inference('simplify', [status(thm)], ['91'])).
% 19.48/19.68  thf('93', plain,
% 19.48/19.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 19.48/19.68      inference('sup-', [status(thm)], ['30', '31'])).
% 19.48/19.68  thf('94', plain,
% 19.48/19.68      (![X10 : $i]:
% 19.48/19.68         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 19.48/19.68      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 19.48/19.68  thf('95', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (((k1_xboole_0) = (X0))
% 19.48/19.68          | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))
% 19.48/19.68          | ~ (v1_relat_1 @ X0))),
% 19.48/19.68      inference('sup+', [status(thm)], ['93', '94'])).
% 19.48/19.68  thf('96', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X0)
% 19.48/19.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 19.48/19.68          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 19.48/19.68      inference('sup-', [status(thm)], ['92', '95'])).
% 19.48/19.68  thf('97', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ k1_xboole_0)
% 19.48/19.68          | ~ (v1_relat_1 @ X0)
% 19.48/19.68          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 19.48/19.68          | ~ (v1_relat_1 @ X0))),
% 19.48/19.68      inference('sup-', [status(thm)], ['67', '96'])).
% 19.48/19.68  thf('98', plain, ((v1_relat_1 @ k1_xboole_0)),
% 19.48/19.68      inference('demod', [status(thm)], ['54', '55'])).
% 19.48/19.68  thf('99', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X0)
% 19.48/19.68          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 19.48/19.68          | ~ (v1_relat_1 @ X0))),
% 19.48/19.68      inference('demod', [status(thm)], ['97', '98'])).
% 19.48/19.68  thf('100', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 19.48/19.68          | ~ (v1_relat_1 @ X0))),
% 19.48/19.68      inference('simplify', [status(thm)], ['99'])).
% 19.48/19.68  thf('101', plain,
% 19.48/19.68      (![X0 : $i, X1 : $i]:
% 19.48/19.68         (((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 19.48/19.68          | ~ (v1_xboole_0 @ X0)
% 19.48/19.68          | ~ (v1_relat_1 @ X1))),
% 19.48/19.68      inference('sup+', [status(thm)], ['66', '100'])).
% 19.48/19.68  thf('102', plain,
% 19.48/19.68      (![X0 : $i, X1 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X0)
% 19.48/19.68          | ~ (v1_xboole_0 @ X1)
% 19.48/19.68          | ((k1_xboole_0) = (k5_relat_1 @ (k4_relat_1 @ X0) @ X1)))),
% 19.48/19.68      inference('sup-', [status(thm)], ['65', '101'])).
% 19.48/19.68  thf('103', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 19.48/19.68          | ~ (v1_relat_1 @ X0)
% 19.48/19.68          | ~ (v1_xboole_0 @ k1_xboole_0)
% 19.48/19.68          | ~ (v1_relat_1 @ X0))),
% 19.48/19.68      inference('sup+', [status(thm)], ['64', '102'])).
% 19.48/19.68  thf('104', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.48/19.68      inference('demod', [status(thm)], ['5', '8'])).
% 19.48/19.68  thf('105', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 19.48/19.68          | ~ (v1_relat_1 @ X0)
% 19.48/19.68          | ~ (v1_relat_1 @ X0))),
% 19.48/19.68      inference('demod', [status(thm)], ['103', '104'])).
% 19.48/19.68  thf('106', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X0)
% 19.48/19.68          | ((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 19.48/19.68      inference('simplify', [status(thm)], ['105'])).
% 19.48/19.68  thf('107', plain,
% 19.48/19.68      (![X10 : $i]:
% 19.48/19.68         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 19.48/19.68      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 19.48/19.68  thf('108', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 19.48/19.68          | ~ (v1_relat_1 @ X0)
% 19.48/19.68          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 19.48/19.68      inference('sup+', [status(thm)], ['106', '107'])).
% 19.48/19.68  thf('109', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.48/19.68      inference('demod', [status(thm)], ['58', '59'])).
% 19.48/19.68  thf('110', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 19.48/19.68          | ~ (v1_relat_1 @ X0)
% 19.48/19.68          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 19.48/19.68      inference('demod', [status(thm)], ['108', '109'])).
% 19.48/19.68  thf('111', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X0)
% 19.48/19.68          | ~ (v1_relat_1 @ k1_xboole_0)
% 19.48/19.68          | ~ (v1_relat_1 @ X0)
% 19.48/19.68          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 19.48/19.68      inference('sup-', [status(thm)], ['0', '110'])).
% 19.48/19.68  thf('112', plain, ((v1_relat_1 @ k1_xboole_0)),
% 19.48/19.68      inference('demod', [status(thm)], ['54', '55'])).
% 19.48/19.68  thf('113', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (~ (v1_relat_1 @ X0)
% 19.48/19.68          | ~ (v1_relat_1 @ X0)
% 19.48/19.68          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 19.48/19.68      inference('demod', [status(thm)], ['111', '112'])).
% 19.48/19.68  thf('114', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 19.48/19.68          | ~ (v1_relat_1 @ X0))),
% 19.48/19.68      inference('simplify', [status(thm)], ['113'])).
% 19.48/19.68  thf('115', plain,
% 19.48/19.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.48/19.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 19.48/19.68  thf(t62_relat_1, conjecture,
% 19.48/19.68    (![A:$i]:
% 19.48/19.68     ( ( v1_relat_1 @ A ) =>
% 19.48/19.68       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 19.48/19.68         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 19.48/19.68  thf(zf_stmt_0, negated_conjecture,
% 19.48/19.68    (~( ![A:$i]:
% 19.48/19.68        ( ( v1_relat_1 @ A ) =>
% 19.48/19.68          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 19.48/19.68            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 19.48/19.68    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 19.48/19.68  thf('116', plain,
% 19.48/19.68      ((((k5_relat_1 @ k1_xboole_0 @ sk_A_1) != (k1_xboole_0))
% 19.48/19.68        | ((k5_relat_1 @ sk_A_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 19.48/19.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.48/19.68  thf('117', plain,
% 19.48/19.68      ((((k5_relat_1 @ k1_xboole_0 @ sk_A_1) != (k1_xboole_0)))
% 19.48/19.68         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 19.48/19.68      inference('split', [status(esa)], ['116'])).
% 19.48/19.68  thf('118', plain,
% 19.48/19.68      ((![X0 : $i]:
% 19.48/19.68          (((k5_relat_1 @ X0 @ sk_A_1) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 19.48/19.68         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 19.48/19.68      inference('sup-', [status(thm)], ['115', '117'])).
% 19.48/19.68  thf('119', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 19.48/19.68          | ~ (v1_relat_1 @ X0))),
% 19.48/19.68      inference('simplify', [status(thm)], ['99'])).
% 19.48/19.68  thf('120', plain,
% 19.48/19.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.48/19.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 19.48/19.68  thf('121', plain,
% 19.48/19.68      ((((k5_relat_1 @ sk_A_1 @ k1_xboole_0) != (k1_xboole_0)))
% 19.48/19.68         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 19.48/19.68      inference('split', [status(esa)], ['116'])).
% 19.48/19.68  thf('122', plain,
% 19.48/19.68      ((![X0 : $i]:
% 19.48/19.68          (((k5_relat_1 @ sk_A_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 19.48/19.68         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 19.48/19.68      inference('sup-', [status(thm)], ['120', '121'])).
% 19.48/19.68  thf('123', plain,
% 19.48/19.68      (((((k1_xboole_0) != (k1_xboole_0))
% 19.48/19.68         | ~ (v1_relat_1 @ sk_A_1)
% 19.48/19.68         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 19.48/19.68         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 19.48/19.68      inference('sup-', [status(thm)], ['119', '122'])).
% 19.48/19.68  thf('124', plain, ((v1_relat_1 @ sk_A_1)),
% 19.48/19.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.48/19.68  thf('125', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.48/19.68      inference('demod', [status(thm)], ['5', '8'])).
% 19.48/19.68  thf('126', plain,
% 19.48/19.68      ((((k1_xboole_0) != (k1_xboole_0)))
% 19.48/19.68         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 19.48/19.68      inference('demod', [status(thm)], ['123', '124', '125'])).
% 19.48/19.68  thf('127', plain, ((((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 19.48/19.68      inference('simplify', [status(thm)], ['126'])).
% 19.48/19.68  thf('128', plain,
% 19.48/19.68      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))) | 
% 19.48/19.68       ~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 19.48/19.68      inference('split', [status(esa)], ['116'])).
% 19.48/19.68  thf('129', plain,
% 19.48/19.68      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0)))),
% 19.48/19.68      inference('sat_resolution*', [status(thm)], ['127', '128'])).
% 19.48/19.68  thf('130', plain,
% 19.48/19.68      (![X0 : $i]:
% 19.48/19.68         (((k5_relat_1 @ X0 @ sk_A_1) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.48/19.68      inference('simpl_trail', [status(thm)], ['118', '129'])).
% 19.48/19.68  thf('131', plain,
% 19.48/19.68      ((((k1_xboole_0) != (k1_xboole_0))
% 19.48/19.68        | ~ (v1_relat_1 @ sk_A_1)
% 19.48/19.68        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 19.48/19.68      inference('sup-', [status(thm)], ['114', '130'])).
% 19.48/19.68  thf('132', plain, ((v1_relat_1 @ sk_A_1)),
% 19.48/19.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.48/19.68  thf('133', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.48/19.68      inference('demod', [status(thm)], ['5', '8'])).
% 19.48/19.68  thf('134', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 19.48/19.68      inference('demod', [status(thm)], ['131', '132', '133'])).
% 19.48/19.68  thf('135', plain, ($false), inference('simplify', [status(thm)], ['134'])).
% 19.48/19.68  
% 19.48/19.68  % SZS output end Refutation
% 19.48/19.68  
% 19.48/19.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
