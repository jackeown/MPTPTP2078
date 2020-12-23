%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ahu8pIQt4i

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:29 EST 2020

% Result     : Theorem 20.69s
% Output     : Refutation 20.69s
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

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
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
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
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
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
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
      ( ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
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
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

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
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','36'])).

thf('38',plain,(
    ! [X10: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k2_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['5','8'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
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
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k1_relat_1 @ X0 ) )
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
      | ( v1_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ),
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
      ( ( ( k4_relat_1 @ ( k2_relat_1 @ X0 ) )
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
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
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
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('71',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['5','8'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
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
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('81',plain,(
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('82',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['5','8'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','88'])).

thf('90',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
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
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','96'])).

thf('98',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
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
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
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
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','110'])).

thf('112',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
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
    ( ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('121',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['116'])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A_1 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
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
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['116'])).

thf('129',plain,(
    ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A_1 @ X0 )
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ahu8pIQt4i
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:09:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 20.69/20.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 20.69/20.87  % Solved by: fo/fo7.sh
% 20.69/20.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.69/20.87  % done 15788 iterations in 20.397s
% 20.69/20.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 20.69/20.87  % SZS output start Refutation
% 20.69/20.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 20.69/20.87  thf(sk_A_type, type, sk_A: $i).
% 20.69/20.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 20.69/20.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 20.69/20.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 20.69/20.87  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 20.69/20.87  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 20.69/20.87  thf(sk_A_1_type, type, sk_A_1: $i).
% 20.69/20.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 20.69/20.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 20.69/20.87  thf(dt_k5_relat_1, axiom,
% 20.69/20.87    (![A:$i,B:$i]:
% 20.69/20.87     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 20.69/20.87       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 20.69/20.87  thf('0', plain,
% 20.69/20.87      (![X7 : $i, X8 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X7)
% 20.69/20.87          | ~ (v1_relat_1 @ X8)
% 20.69/20.87          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 20.69/20.87      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 20.69/20.87  thf(t60_relat_1, axiom,
% 20.69/20.87    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 20.69/20.87     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 20.69/20.87  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 20.69/20.87      inference('cnf', [status(esa)], [t60_relat_1])).
% 20.69/20.87  thf(l13_xboole_0, axiom,
% 20.69/20.87    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 20.69/20.87  thf('2', plain,
% 20.69/20.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('cnf', [status(esa)], [l13_xboole_0])).
% 20.69/20.87  thf('3', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 20.69/20.87      inference('cnf', [status(esa)], [t60_relat_1])).
% 20.69/20.87  thf('4', plain,
% 20.69/20.87      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['2', '3'])).
% 20.69/20.87  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 20.69/20.87  thf('5', plain, ((v1_xboole_0 @ sk_A)),
% 20.69/20.87      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 20.69/20.87  thf('6', plain, ((v1_xboole_0 @ sk_A)),
% 20.69/20.87      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 20.69/20.87  thf('7', plain,
% 20.69/20.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('cnf', [status(esa)], [l13_xboole_0])).
% 20.69/20.87  thf('8', plain, (((sk_A) = (k1_xboole_0))),
% 20.69/20.87      inference('sup-', [status(thm)], ['6', '7'])).
% 20.69/20.87  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['5', '8'])).
% 20.69/20.87  thf('10', plain,
% 20.69/20.87      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['4', '9'])).
% 20.69/20.87  thf(dt_k4_relat_1, axiom,
% 20.69/20.87    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 20.69/20.87  thf('11', plain,
% 20.69/20.87      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 20.69/20.87      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 20.69/20.87  thf('12', plain,
% 20.69/20.87      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 20.69/20.87      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 20.69/20.87  thf(involutiveness_k4_relat_1, axiom,
% 20.69/20.87    (![A:$i]:
% 20.69/20.87     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 20.69/20.87  thf('13', plain,
% 20.69/20.87      (![X10 : $i]:
% 20.69/20.87         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 20.69/20.87      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 20.69/20.87  thf(t37_relat_1, axiom,
% 20.69/20.87    (![A:$i]:
% 20.69/20.87     ( ( v1_relat_1 @ A ) =>
% 20.69/20.87       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 20.69/20.87         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 20.69/20.87  thf('14', plain,
% 20.69/20.87      (![X11 : $i]:
% 20.69/20.87         (((k2_relat_1 @ X11) = (k1_relat_1 @ (k4_relat_1 @ X11)))
% 20.69/20.87          | ~ (v1_relat_1 @ X11))),
% 20.69/20.87      inference('cnf', [status(esa)], [t37_relat_1])).
% 20.69/20.87  thf('15', plain,
% 20.69/20.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('cnf', [status(esa)], [l13_xboole_0])).
% 20.69/20.87  thf('16', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 20.69/20.87      inference('cnf', [status(esa)], [t60_relat_1])).
% 20.69/20.87  thf('17', plain,
% 20.69/20.87      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['15', '16'])).
% 20.69/20.87  thf('18', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_xboole_0 @ (k4_relat_1 @ X0)))),
% 20.69/20.87      inference('sup+', [status(thm)], ['14', '17'])).
% 20.69/20.87  thf('19', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_xboole_0 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 20.69/20.87          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_xboole_0)))),
% 20.69/20.87      inference('sup-', [status(thm)], ['13', '18'])).
% 20.69/20.87  thf('20', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X0)
% 20.69/20.87          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_xboole_0))
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('sup-', [status(thm)], ['12', '19'])).
% 20.69/20.87  thf('21', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_xboole_0 @ X0)
% 20.69/20.87          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_xboole_0))
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('simplify', [status(thm)], ['20'])).
% 20.69/20.87  thf(cc1_relat_1, axiom,
% 20.69/20.87    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 20.69/20.87  thf('22', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 20.69/20.87      inference('cnf', [status(esa)], [cc1_relat_1])).
% 20.69/20.87  thf('23', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_xboole_0))
% 20.69/20.87          | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('clc', [status(thm)], ['21', '22'])).
% 20.69/20.87  thf(fc9_relat_1, axiom,
% 20.69/20.87    (![A:$i]:
% 20.69/20.87     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 20.69/20.87       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 20.69/20.87  thf('24', plain,
% 20.69/20.87      (![X9 : $i]:
% 20.69/20.87         (~ (v1_xboole_0 @ (k2_relat_1 @ X9))
% 20.69/20.87          | ~ (v1_relat_1 @ X9)
% 20.69/20.87          | (v1_xboole_0 @ X9))),
% 20.69/20.87      inference('cnf', [status(esa)], [fc9_relat_1])).
% 20.69/20.87  thf('25', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_xboole_0 @ k1_xboole_0)
% 20.69/20.87          | ~ (v1_xboole_0 @ X0)
% 20.69/20.87          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 20.69/20.87          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 20.69/20.87      inference('sup-', [status(thm)], ['23', '24'])).
% 20.69/20.87  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['5', '8'])).
% 20.69/20.87  thf('27', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_xboole_0 @ X0)
% 20.69/20.87          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 20.69/20.87          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 20.69/20.87      inference('demod', [status(thm)], ['25', '26'])).
% 20.69/20.87  thf('28', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X0)
% 20.69/20.87          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 20.69/20.87          | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('sup-', [status(thm)], ['11', '27'])).
% 20.69/20.87  thf('29', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 20.69/20.87      inference('cnf', [status(esa)], [cc1_relat_1])).
% 20.69/20.87  thf('30', plain,
% 20.69/20.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k4_relat_1 @ X0)))),
% 20.69/20.87      inference('clc', [status(thm)], ['28', '29'])).
% 20.69/20.87  thf('31', plain,
% 20.69/20.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('cnf', [status(esa)], [l13_xboole_0])).
% 20.69/20.87  thf('32', plain,
% 20.69/20.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 20.69/20.87      inference('sup-', [status(thm)], ['30', '31'])).
% 20.69/20.87  thf('33', plain,
% 20.69/20.87      (![X10 : $i]:
% 20.69/20.87         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 20.69/20.87      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 20.69/20.87  thf('34', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k4_relat_1 @ k1_xboole_0) = (X0))
% 20.69/20.87          | ~ (v1_xboole_0 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['32', '33'])).
% 20.69/20.87  thf('35', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 20.69/20.87      inference('cnf', [status(esa)], [cc1_relat_1])).
% 20.69/20.87  thf('36', plain,
% 20.69/20.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ k1_xboole_0) = (X0)))),
% 20.69/20.87      inference('clc', [status(thm)], ['34', '35'])).
% 20.69/20.87  thf('37', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_xboole_0 @ X0)
% 20.69/20.87          | ((k4_relat_1 @ k1_xboole_0) = (k2_relat_1 @ X0)))),
% 20.69/20.87      inference('sup-', [status(thm)], ['10', '36'])).
% 20.69/20.87  thf('38', plain,
% 20.69/20.87      (![X10 : $i]:
% 20.69/20.87         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 20.69/20.87      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 20.69/20.87  thf('39', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k4_relat_1 @ (k2_relat_1 @ X0)) = (k1_xboole_0))
% 20.69/20.87          | ~ (v1_xboole_0 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ k1_xboole_0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['37', '38'])).
% 20.69/20.87  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 20.69/20.87      inference('cnf', [status(esa)], [t60_relat_1])).
% 20.69/20.87  thf('41', plain,
% 20.69/20.87      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['15', '16'])).
% 20.69/20.87  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['5', '8'])).
% 20.69/20.87  thf('43', plain,
% 20.69/20.87      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['41', '42'])).
% 20.69/20.87  thf('44', plain,
% 20.69/20.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ k1_xboole_0) = (X0)))),
% 20.69/20.87      inference('clc', [status(thm)], ['34', '35'])).
% 20.69/20.87  thf('45', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_xboole_0 @ X0)
% 20.69/20.87          | ((k4_relat_1 @ k1_xboole_0) = (k1_relat_1 @ X0)))),
% 20.69/20.87      inference('sup-', [status(thm)], ['43', '44'])).
% 20.69/20.87  thf('46', plain,
% 20.69/20.87      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 20.69/20.87      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 20.69/20.87  thf('47', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         ((v1_relat_1 @ (k1_relat_1 @ X0))
% 20.69/20.87          | ~ (v1_xboole_0 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ k1_xboole_0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['45', '46'])).
% 20.69/20.87  thf('48', plain,
% 20.69/20.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 20.69/20.87      inference('sup-', [status(thm)], ['30', '31'])).
% 20.69/20.87  thf('49', plain,
% 20.69/20.87      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 20.69/20.87      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 20.69/20.87  thf('50', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         ((v1_relat_1 @ k1_xboole_0)
% 20.69/20.87          | ~ (v1_xboole_0 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['48', '49'])).
% 20.69/20.87  thf('51', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 20.69/20.87      inference('cnf', [status(esa)], [cc1_relat_1])).
% 20.69/20.87  thf('52', plain,
% 20.69/20.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 20.69/20.87      inference('clc', [status(thm)], ['50', '51'])).
% 20.69/20.87  thf('53', plain,
% 20.69/20.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ (k1_relat_1 @ X0)))),
% 20.69/20.87      inference('clc', [status(thm)], ['47', '52'])).
% 20.69/20.87  thf('54', plain,
% 20.69/20.87      (((v1_relat_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['40', '53'])).
% 20.69/20.87  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['5', '8'])).
% 20.69/20.87  thf('56', plain, ((v1_relat_1 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['54', '55'])).
% 20.69/20.87  thf('57', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k4_relat_1 @ (k2_relat_1 @ X0)) = (k1_xboole_0))
% 20.69/20.87          | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('demod', [status(thm)], ['39', '56'])).
% 20.69/20.87  thf('58', plain,
% 20.69/20.87      ((((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 20.69/20.87        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['1', '57'])).
% 20.69/20.87  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['5', '8'])).
% 20.69/20.87  thf('60', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 20.69/20.87      inference('demod', [status(thm)], ['58', '59'])).
% 20.69/20.87  thf(t54_relat_1, axiom,
% 20.69/20.87    (![A:$i]:
% 20.69/20.87     ( ( v1_relat_1 @ A ) =>
% 20.69/20.87       ( ![B:$i]:
% 20.69/20.87         ( ( v1_relat_1 @ B ) =>
% 20.69/20.87           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 20.69/20.87             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 20.69/20.87  thf('61', plain,
% 20.69/20.87      (![X14 : $i, X15 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X14)
% 20.69/20.87          | ((k4_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 20.69/20.87              = (k5_relat_1 @ (k4_relat_1 @ X14) @ (k4_relat_1 @ X15)))
% 20.69/20.87          | ~ (v1_relat_1 @ X15))),
% 20.69/20.87      inference('cnf', [status(esa)], [t54_relat_1])).
% 20.69/20.87  thf('62', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 20.69/20.87            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ k1_xboole_0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['60', '61'])).
% 20.69/20.87  thf('63', plain, ((v1_relat_1 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['54', '55'])).
% 20.69/20.87  thf('64', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 20.69/20.87            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('demod', [status(thm)], ['62', '63'])).
% 20.69/20.87  thf('65', plain,
% 20.69/20.87      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 20.69/20.87      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 20.69/20.87  thf('66', plain,
% 20.69/20.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('cnf', [status(esa)], [l13_xboole_0])).
% 20.69/20.87  thf('67', plain,
% 20.69/20.87      (![X7 : $i, X8 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X7)
% 20.69/20.87          | ~ (v1_relat_1 @ X8)
% 20.69/20.87          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 20.69/20.87      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 20.69/20.87  thf('68', plain,
% 20.69/20.87      (![X7 : $i, X8 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X7)
% 20.69/20.87          | ~ (v1_relat_1 @ X8)
% 20.69/20.87          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 20.69/20.87      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 20.69/20.87  thf('69', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 20.69/20.87      inference('cnf', [status(esa)], [cc1_relat_1])).
% 20.69/20.87  thf('70', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 20.69/20.87      inference('cnf', [status(esa)], [t60_relat_1])).
% 20.69/20.87  thf(t44_relat_1, axiom,
% 20.69/20.87    (![A:$i]:
% 20.69/20.87     ( ( v1_relat_1 @ A ) =>
% 20.69/20.87       ( ![B:$i]:
% 20.69/20.87         ( ( v1_relat_1 @ B ) =>
% 20.69/20.87           ( r1_tarski @
% 20.69/20.87             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 20.69/20.87  thf('71', plain,
% 20.69/20.87      (![X12 : $i, X13 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X12)
% 20.69/20.87          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X13 @ X12)) @ 
% 20.69/20.87             (k1_relat_1 @ X13))
% 20.69/20.87          | ~ (v1_relat_1 @ X13))),
% 20.69/20.87      inference('cnf', [status(esa)], [t44_relat_1])).
% 20.69/20.87  thf('72', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 20.69/20.87           k1_xboole_0)
% 20.69/20.87          | ~ (v1_relat_1 @ k1_xboole_0)
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['70', '71'])).
% 20.69/20.87  thf('73', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_xboole_0 @ k1_xboole_0)
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 20.69/20.87             k1_xboole_0))),
% 20.69/20.87      inference('sup-', [status(thm)], ['69', '72'])).
% 20.69/20.87  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['5', '8'])).
% 20.69/20.87  thf('75', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X0)
% 20.69/20.87          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 20.69/20.87             k1_xboole_0))),
% 20.69/20.87      inference('demod', [status(thm)], ['73', '74'])).
% 20.69/20.87  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 20.69/20.87  thf('76', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 20.69/20.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 20.69/20.87  thf(d10_xboole_0, axiom,
% 20.69/20.87    (![A:$i,B:$i]:
% 20.69/20.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 20.69/20.87  thf('77', plain,
% 20.69/20.87      (![X1 : $i, X3 : $i]:
% 20.69/20.87         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 20.69/20.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 20.69/20.87  thf('78', plain,
% 20.69/20.87      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 20.69/20.87      inference('sup-', [status(thm)], ['76', '77'])).
% 20.69/20.87  thf('79', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X0)
% 20.69/20.87          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 20.69/20.87      inference('sup-', [status(thm)], ['75', '78'])).
% 20.69/20.87  thf('80', plain,
% 20.69/20.87      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 20.69/20.87      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 20.69/20.87  thf('81', plain,
% 20.69/20.87      (![X11 : $i]:
% 20.69/20.87         (((k1_relat_1 @ X11) = (k2_relat_1 @ (k4_relat_1 @ X11)))
% 20.69/20.87          | ~ (v1_relat_1 @ X11))),
% 20.69/20.87      inference('cnf', [status(esa)], [t37_relat_1])).
% 20.69/20.87  thf('82', plain,
% 20.69/20.87      (![X9 : $i]:
% 20.69/20.87         (~ (v1_xboole_0 @ (k2_relat_1 @ X9))
% 20.69/20.87          | ~ (v1_relat_1 @ X9)
% 20.69/20.87          | (v1_xboole_0 @ X9))),
% 20.69/20.87      inference('cnf', [status(esa)], [fc9_relat_1])).
% 20.69/20.87  thf('83', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 20.69/20.87          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 20.69/20.87      inference('sup-', [status(thm)], ['81', '82'])).
% 20.69/20.87  thf('84', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X0)
% 20.69/20.87          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 20.69/20.87      inference('sup-', [status(thm)], ['80', '83'])).
% 20.69/20.87  thf('85', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 20.69/20.87          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('simplify', [status(thm)], ['84'])).
% 20.69/20.87  thf('86', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_xboole_0 @ k1_xboole_0)
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 20.69/20.87          | (v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 20.69/20.87      inference('sup-', [status(thm)], ['79', '85'])).
% 20.69/20.87  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['5', '8'])).
% 20.69/20.87  thf('88', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 20.69/20.87          | (v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 20.69/20.87      inference('demod', [status(thm)], ['86', '87'])).
% 20.69/20.87  thf('89', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ k1_xboole_0)
% 20.69/20.87          | (v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('sup-', [status(thm)], ['68', '88'])).
% 20.69/20.87  thf('90', plain, ((v1_relat_1 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['54', '55'])).
% 20.69/20.87  thf('91', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X0)
% 20.69/20.87          | (v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('demod', [status(thm)], ['89', '90'])).
% 20.69/20.87  thf('92', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         ((v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('simplify', [status(thm)], ['91'])).
% 20.69/20.87  thf('93', plain,
% 20.69/20.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 20.69/20.87      inference('sup-', [status(thm)], ['30', '31'])).
% 20.69/20.87  thf('94', plain,
% 20.69/20.87      (![X10 : $i]:
% 20.69/20.87         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 20.69/20.87      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 20.69/20.87  thf('95', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k1_xboole_0) = (X0))
% 20.69/20.87          | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['93', '94'])).
% 20.69/20.87  thf('96', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 20.69/20.87          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 20.69/20.87      inference('sup-', [status(thm)], ['92', '95'])).
% 20.69/20.87  thf('97', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ k1_xboole_0)
% 20.69/20.87          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('sup-', [status(thm)], ['67', '96'])).
% 20.69/20.87  thf('98', plain, ((v1_relat_1 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['54', '55'])).
% 20.69/20.87  thf('99', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X0)
% 20.69/20.87          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('demod', [status(thm)], ['97', '98'])).
% 20.69/20.87  thf('100', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('simplify', [status(thm)], ['99'])).
% 20.69/20.87  thf('101', plain,
% 20.69/20.87      (![X0 : $i, X1 : $i]:
% 20.69/20.87         (((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 20.69/20.87          | ~ (v1_xboole_0 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ X1))),
% 20.69/20.87      inference('sup+', [status(thm)], ['66', '100'])).
% 20.69/20.87  thf('102', plain,
% 20.69/20.87      (![X0 : $i, X1 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_xboole_0 @ X1)
% 20.69/20.87          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))))),
% 20.69/20.87      inference('sup-', [status(thm)], ['65', '101'])).
% 20.69/20.87  thf('103', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_xboole_0 @ k1_xboole_0)
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('sup+', [status(thm)], ['64', '102'])).
% 20.69/20.87  thf('104', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['5', '8'])).
% 20.69/20.87  thf('105', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('demod', [status(thm)], ['103', '104'])).
% 20.69/20.87  thf('106', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X0)
% 20.69/20.87          | ((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 20.69/20.87      inference('simplify', [status(thm)], ['105'])).
% 20.69/20.87  thf('107', plain,
% 20.69/20.87      (![X10 : $i]:
% 20.69/20.87         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 20.69/20.87      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 20.69/20.87  thf('108', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 20.69/20.87      inference('sup+', [status(thm)], ['106', '107'])).
% 20.69/20.87  thf('109', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 20.69/20.87      inference('demod', [status(thm)], ['58', '59'])).
% 20.69/20.87  thf('110', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 20.69/20.87      inference('demod', [status(thm)], ['108', '109'])).
% 20.69/20.87  thf('111', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ k1_xboole_0)
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 20.69/20.87      inference('sup-', [status(thm)], ['0', '110'])).
% 20.69/20.87  thf('112', plain, ((v1_relat_1 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['54', '55'])).
% 20.69/20.87  thf('113', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (~ (v1_relat_1 @ X0)
% 20.69/20.87          | ~ (v1_relat_1 @ X0)
% 20.69/20.87          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 20.69/20.87      inference('demod', [status(thm)], ['111', '112'])).
% 20.69/20.87  thf('114', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('simplify', [status(thm)], ['113'])).
% 20.69/20.87  thf('115', plain,
% 20.69/20.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('cnf', [status(esa)], [l13_xboole_0])).
% 20.69/20.87  thf(t62_relat_1, conjecture,
% 20.69/20.87    (![A:$i]:
% 20.69/20.87     ( ( v1_relat_1 @ A ) =>
% 20.69/20.87       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 20.69/20.87         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 20.69/20.87  thf(zf_stmt_0, negated_conjecture,
% 20.69/20.87    (~( ![A:$i]:
% 20.69/20.87        ( ( v1_relat_1 @ A ) =>
% 20.69/20.87          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 20.69/20.87            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 20.69/20.87    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 20.69/20.87  thf('116', plain,
% 20.69/20.87      ((((k5_relat_1 @ k1_xboole_0 @ sk_A_1) != (k1_xboole_0))
% 20.69/20.87        | ((k5_relat_1 @ sk_A_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 20.69/20.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.69/20.87  thf('117', plain,
% 20.69/20.87      ((((k5_relat_1 @ sk_A_1 @ k1_xboole_0) != (k1_xboole_0)))
% 20.69/20.87         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 20.69/20.87      inference('split', [status(esa)], ['116'])).
% 20.69/20.87  thf('118', plain,
% 20.69/20.87      ((![X0 : $i]:
% 20.69/20.87          (((k5_relat_1 @ sk_A_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 20.69/20.87         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 20.69/20.87      inference('sup-', [status(thm)], ['115', '117'])).
% 20.69/20.87  thf('119', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 20.69/20.87          | ~ (v1_relat_1 @ X0))),
% 20.69/20.87      inference('simplify', [status(thm)], ['99'])).
% 20.69/20.87  thf('120', plain,
% 20.69/20.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('cnf', [status(esa)], [l13_xboole_0])).
% 20.69/20.87  thf('121', plain,
% 20.69/20.87      ((((k5_relat_1 @ k1_xboole_0 @ sk_A_1) != (k1_xboole_0)))
% 20.69/20.87         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 20.69/20.87      inference('split', [status(esa)], ['116'])).
% 20.69/20.87  thf('122', plain,
% 20.69/20.87      ((![X0 : $i]:
% 20.69/20.87          (((k5_relat_1 @ X0 @ sk_A_1) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 20.69/20.87         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 20.69/20.87      inference('sup-', [status(thm)], ['120', '121'])).
% 20.69/20.87  thf('123', plain,
% 20.69/20.87      (((((k1_xboole_0) != (k1_xboole_0))
% 20.69/20.87         | ~ (v1_relat_1 @ sk_A_1)
% 20.69/20.87         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 20.69/20.87         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 20.69/20.87      inference('sup-', [status(thm)], ['119', '122'])).
% 20.69/20.87  thf('124', plain, ((v1_relat_1 @ sk_A_1)),
% 20.69/20.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.69/20.87  thf('125', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['5', '8'])).
% 20.69/20.87  thf('126', plain,
% 20.69/20.87      ((((k1_xboole_0) != (k1_xboole_0)))
% 20.69/20.87         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 20.69/20.87      inference('demod', [status(thm)], ['123', '124', '125'])).
% 20.69/20.87  thf('127', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0)))),
% 20.69/20.87      inference('simplify', [status(thm)], ['126'])).
% 20.69/20.87  thf('128', plain,
% 20.69/20.87      (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 20.69/20.87       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0)))),
% 20.69/20.87      inference('split', [status(esa)], ['116'])).
% 20.69/20.87  thf('129', plain,
% 20.69/20.87      (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 20.69/20.87      inference('sat_resolution*', [status(thm)], ['127', '128'])).
% 20.69/20.87  thf('130', plain,
% 20.69/20.87      (![X0 : $i]:
% 20.69/20.87         (((k5_relat_1 @ sk_A_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 20.69/20.87      inference('simpl_trail', [status(thm)], ['118', '129'])).
% 20.69/20.87  thf('131', plain,
% 20.69/20.87      ((((k1_xboole_0) != (k1_xboole_0))
% 20.69/20.87        | ~ (v1_relat_1 @ sk_A_1)
% 20.69/20.87        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 20.69/20.87      inference('sup-', [status(thm)], ['114', '130'])).
% 20.69/20.87  thf('132', plain, ((v1_relat_1 @ sk_A_1)),
% 20.69/20.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.69/20.87  thf('133', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 20.69/20.87      inference('demod', [status(thm)], ['5', '8'])).
% 20.69/20.87  thf('134', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 20.69/20.87      inference('demod', [status(thm)], ['131', '132', '133'])).
% 20.69/20.87  thf('135', plain, ($false), inference('simplify', [status(thm)], ['134'])).
% 20.69/20.87  
% 20.69/20.87  % SZS output end Refutation
% 20.69/20.87  
% 20.69/20.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
