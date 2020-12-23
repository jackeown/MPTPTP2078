%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x1JphPWXnU

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:28 EST 2020

% Result     : Theorem 19.22s
% Output     : Refutation 19.22s
% Verified   : 
% Statistics : Number of formulae       :  156 (1115 expanded)
%              Number of leaves         :   23 ( 366 expanded)
%              Depth                    :   38
%              Number of atoms          : 1005 (6885 expanded)
%              Number of equality atoms :   94 ( 633 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('8',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
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

thf('10',plain,(
    ! [X11: $i] :
      ( ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('18',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

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
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','23'])).

thf('25',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X10: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','32'])).

thf('34',plain,(
    ! [X10: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k2_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('45',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['43','48'])).

thf('50',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k2_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','52'])).

thf('54',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

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
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('63',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('64',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('65',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('66',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('67',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('72',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('77',plain,(
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('78',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','84'])).

thf('86',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('90',plain,(
    ! [X10: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','92'])).

thf('94',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','98'])).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X10: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','106'])).

thf('108',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
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

thf('112',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('117',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['112'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('122',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['112'])).

thf('125',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['114','125'])).

thf('127',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('130',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    $false ),
    inference(simplify,[status(thm)],['130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x1JphPWXnU
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:01:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 19.22/19.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 19.22/19.44  % Solved by: fo/fo7.sh
% 19.22/19.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.22/19.44  % done 15503 iterations in 18.977s
% 19.22/19.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 19.22/19.44  % SZS output start Refutation
% 19.22/19.44  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 19.22/19.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 19.22/19.44  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 19.22/19.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.22/19.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 19.22/19.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 19.22/19.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 19.22/19.44  thf(sk_A_type, type, sk_A: $i).
% 19.22/19.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 19.22/19.44  thf(dt_k5_relat_1, axiom,
% 19.22/19.44    (![A:$i,B:$i]:
% 19.22/19.44     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 19.22/19.44       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 19.22/19.44  thf('0', plain,
% 19.22/19.44      (![X7 : $i, X8 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X7)
% 19.22/19.44          | ~ (v1_relat_1 @ X8)
% 19.22/19.44          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 19.22/19.44      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 19.22/19.44  thf(t60_relat_1, axiom,
% 19.22/19.44    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 19.22/19.44     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 19.22/19.44  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.22/19.44      inference('cnf', [status(esa)], [t60_relat_1])).
% 19.22/19.44  thf(l13_xboole_0, axiom,
% 19.22/19.44    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 19.22/19.44  thf('2', plain,
% 19.22/19.44      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('cnf', [status(esa)], [l13_xboole_0])).
% 19.22/19.44  thf('3', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.22/19.44      inference('cnf', [status(esa)], [t60_relat_1])).
% 19.22/19.44  thf('4', plain,
% 19.22/19.44      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['2', '3'])).
% 19.22/19.44  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 19.22/19.44  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.22/19.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 19.22/19.44  thf('6', plain,
% 19.22/19.44      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['4', '5'])).
% 19.22/19.44  thf(dt_k4_relat_1, axiom,
% 19.22/19.44    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 19.22/19.44  thf('7', plain,
% 19.22/19.44      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 19.22/19.44      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 19.22/19.44  thf('8', plain,
% 19.22/19.44      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 19.22/19.44      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 19.22/19.44  thf(involutiveness_k4_relat_1, axiom,
% 19.22/19.44    (![A:$i]:
% 19.22/19.44     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 19.22/19.44  thf('9', plain,
% 19.22/19.44      (![X10 : $i]:
% 19.22/19.44         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 19.22/19.44      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 19.22/19.44  thf(t37_relat_1, axiom,
% 19.22/19.44    (![A:$i]:
% 19.22/19.44     ( ( v1_relat_1 @ A ) =>
% 19.22/19.44       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 19.22/19.44         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 19.22/19.44  thf('10', plain,
% 19.22/19.44      (![X11 : $i]:
% 19.22/19.44         (((k2_relat_1 @ X11) = (k1_relat_1 @ (k4_relat_1 @ X11)))
% 19.22/19.44          | ~ (v1_relat_1 @ X11))),
% 19.22/19.44      inference('cnf', [status(esa)], [t37_relat_1])).
% 19.22/19.44  thf('11', plain,
% 19.22/19.44      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('cnf', [status(esa)], [l13_xboole_0])).
% 19.22/19.44  thf('12', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.22/19.44      inference('cnf', [status(esa)], [t60_relat_1])).
% 19.22/19.44  thf('13', plain,
% 19.22/19.44      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['11', '12'])).
% 19.22/19.44  thf('14', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_xboole_0 @ (k4_relat_1 @ X0)))),
% 19.22/19.44      inference('sup+', [status(thm)], ['10', '13'])).
% 19.22/19.44  thf('15', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_xboole_0 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 19.22/19.44          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_xboole_0)))),
% 19.22/19.44      inference('sup-', [status(thm)], ['9', '14'])).
% 19.22/19.44  thf('16', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X0)
% 19.22/19.44          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_xboole_0))
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('sup-', [status(thm)], ['8', '15'])).
% 19.22/19.44  thf('17', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_xboole_0 @ X0)
% 19.22/19.44          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_xboole_0))
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('simplify', [status(thm)], ['16'])).
% 19.22/19.44  thf(cc1_relat_1, axiom,
% 19.22/19.44    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 19.22/19.44  thf('18', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 19.22/19.44      inference('cnf', [status(esa)], [cc1_relat_1])).
% 19.22/19.44  thf('19', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_xboole_0))
% 19.22/19.44          | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('clc', [status(thm)], ['17', '18'])).
% 19.22/19.44  thf(fc9_relat_1, axiom,
% 19.22/19.44    (![A:$i]:
% 19.22/19.44     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 19.22/19.44       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 19.22/19.44  thf('20', plain,
% 19.22/19.44      (![X9 : $i]:
% 19.22/19.44         (~ (v1_xboole_0 @ (k2_relat_1 @ X9))
% 19.22/19.44          | ~ (v1_relat_1 @ X9)
% 19.22/19.44          | (v1_xboole_0 @ X9))),
% 19.22/19.44      inference('cnf', [status(esa)], [fc9_relat_1])).
% 19.22/19.44  thf('21', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_xboole_0 @ k1_xboole_0)
% 19.22/19.44          | ~ (v1_xboole_0 @ X0)
% 19.22/19.44          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 19.22/19.44          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 19.22/19.44      inference('sup-', [status(thm)], ['19', '20'])).
% 19.22/19.44  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.22/19.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 19.22/19.44  thf('23', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_xboole_0 @ X0)
% 19.22/19.44          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 19.22/19.44          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 19.22/19.44      inference('demod', [status(thm)], ['21', '22'])).
% 19.22/19.44  thf('24', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X0)
% 19.22/19.44          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 19.22/19.44          | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('sup-', [status(thm)], ['7', '23'])).
% 19.22/19.44  thf('25', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 19.22/19.44      inference('cnf', [status(esa)], [cc1_relat_1])).
% 19.22/19.44  thf('26', plain,
% 19.22/19.44      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k4_relat_1 @ X0)))),
% 19.22/19.44      inference('clc', [status(thm)], ['24', '25'])).
% 19.22/19.44  thf('27', plain,
% 19.22/19.44      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('cnf', [status(esa)], [l13_xboole_0])).
% 19.22/19.44  thf('28', plain,
% 19.22/19.44      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 19.22/19.44      inference('sup-', [status(thm)], ['26', '27'])).
% 19.22/19.44  thf('29', plain,
% 19.22/19.44      (![X10 : $i]:
% 19.22/19.44         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 19.22/19.44      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 19.22/19.44  thf('30', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k4_relat_1 @ k1_xboole_0) = (X0))
% 19.22/19.44          | ~ (v1_xboole_0 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['28', '29'])).
% 19.22/19.44  thf('31', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 19.22/19.44      inference('cnf', [status(esa)], [cc1_relat_1])).
% 19.22/19.44  thf('32', plain,
% 19.22/19.44      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ k1_xboole_0) = (X0)))),
% 19.22/19.44      inference('clc', [status(thm)], ['30', '31'])).
% 19.22/19.44  thf('33', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_xboole_0 @ X0)
% 19.22/19.44          | ((k4_relat_1 @ k1_xboole_0) = (k2_relat_1 @ X0)))),
% 19.22/19.44      inference('sup-', [status(thm)], ['6', '32'])).
% 19.22/19.44  thf('34', plain,
% 19.22/19.44      (![X10 : $i]:
% 19.22/19.44         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 19.22/19.44      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 19.22/19.44  thf('35', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k4_relat_1 @ (k2_relat_1 @ X0)) = (k1_xboole_0))
% 19.22/19.44          | ~ (v1_xboole_0 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ k1_xboole_0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['33', '34'])).
% 19.22/19.44  thf('36', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.22/19.44      inference('cnf', [status(esa)], [t60_relat_1])).
% 19.22/19.44  thf('37', plain,
% 19.22/19.44      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['11', '12'])).
% 19.22/19.44  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.22/19.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 19.22/19.44  thf('39', plain,
% 19.22/19.44      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['37', '38'])).
% 19.22/19.44  thf('40', plain,
% 19.22/19.44      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ k1_xboole_0) = (X0)))),
% 19.22/19.44      inference('clc', [status(thm)], ['30', '31'])).
% 19.22/19.44  thf('41', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_xboole_0 @ X0)
% 19.22/19.44          | ((k4_relat_1 @ k1_xboole_0) = (k1_relat_1 @ X0)))),
% 19.22/19.44      inference('sup-', [status(thm)], ['39', '40'])).
% 19.22/19.44  thf('42', plain,
% 19.22/19.44      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 19.22/19.44      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 19.22/19.44  thf('43', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         ((v1_relat_1 @ (k1_relat_1 @ X0))
% 19.22/19.44          | ~ (v1_xboole_0 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ k1_xboole_0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['41', '42'])).
% 19.22/19.44  thf('44', plain,
% 19.22/19.44      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 19.22/19.44      inference('sup-', [status(thm)], ['26', '27'])).
% 19.22/19.44  thf('45', plain,
% 19.22/19.44      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 19.22/19.44      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 19.22/19.44  thf('46', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         ((v1_relat_1 @ k1_xboole_0)
% 19.22/19.44          | ~ (v1_xboole_0 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['44', '45'])).
% 19.22/19.44  thf('47', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 19.22/19.44      inference('cnf', [status(esa)], [cc1_relat_1])).
% 19.22/19.44  thf('48', plain,
% 19.22/19.44      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 19.22/19.44      inference('clc', [status(thm)], ['46', '47'])).
% 19.22/19.44  thf('49', plain,
% 19.22/19.44      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ (k1_relat_1 @ X0)))),
% 19.22/19.44      inference('clc', [status(thm)], ['43', '48'])).
% 19.22/19.44  thf('50', plain,
% 19.22/19.44      (((v1_relat_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['36', '49'])).
% 19.22/19.44  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.22/19.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 19.22/19.44  thf('52', plain, ((v1_relat_1 @ k1_xboole_0)),
% 19.22/19.44      inference('demod', [status(thm)], ['50', '51'])).
% 19.22/19.44  thf('53', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k4_relat_1 @ (k2_relat_1 @ X0)) = (k1_xboole_0))
% 19.22/19.44          | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('demod', [status(thm)], ['35', '52'])).
% 19.22/19.44  thf('54', plain,
% 19.22/19.44      ((((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 19.22/19.44        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['1', '53'])).
% 19.22/19.44  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.22/19.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 19.22/19.44  thf('56', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.22/19.44      inference('demod', [status(thm)], ['54', '55'])).
% 19.22/19.44  thf(t54_relat_1, axiom,
% 19.22/19.44    (![A:$i]:
% 19.22/19.44     ( ( v1_relat_1 @ A ) =>
% 19.22/19.44       ( ![B:$i]:
% 19.22/19.44         ( ( v1_relat_1 @ B ) =>
% 19.22/19.44           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 19.22/19.44             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 19.22/19.44  thf('57', plain,
% 19.22/19.44      (![X14 : $i, X15 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X14)
% 19.22/19.44          | ((k4_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 19.22/19.44              = (k5_relat_1 @ (k4_relat_1 @ X14) @ (k4_relat_1 @ X15)))
% 19.22/19.44          | ~ (v1_relat_1 @ X15))),
% 19.22/19.44      inference('cnf', [status(esa)], [t54_relat_1])).
% 19.22/19.44  thf('58', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 19.22/19.44            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ k1_xboole_0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['56', '57'])).
% 19.22/19.44  thf('59', plain, ((v1_relat_1 @ k1_xboole_0)),
% 19.22/19.44      inference('demod', [status(thm)], ['50', '51'])).
% 19.22/19.44  thf('60', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 19.22/19.44            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('demod', [status(thm)], ['58', '59'])).
% 19.22/19.44  thf('61', plain,
% 19.22/19.44      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 19.22/19.44      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 19.22/19.44  thf('62', plain,
% 19.22/19.44      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('cnf', [status(esa)], [l13_xboole_0])).
% 19.22/19.44  thf('63', plain,
% 19.22/19.44      (![X7 : $i, X8 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X7)
% 19.22/19.44          | ~ (v1_relat_1 @ X8)
% 19.22/19.44          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 19.22/19.44      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 19.22/19.44  thf('64', plain,
% 19.22/19.44      (![X7 : $i, X8 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X7)
% 19.22/19.44          | ~ (v1_relat_1 @ X8)
% 19.22/19.44          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 19.22/19.44      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 19.22/19.44  thf('65', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 19.22/19.44      inference('cnf', [status(esa)], [cc1_relat_1])).
% 19.22/19.44  thf('66', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.22/19.44      inference('cnf', [status(esa)], [t60_relat_1])).
% 19.22/19.44  thf(t44_relat_1, axiom,
% 19.22/19.44    (![A:$i]:
% 19.22/19.44     ( ( v1_relat_1 @ A ) =>
% 19.22/19.44       ( ![B:$i]:
% 19.22/19.44         ( ( v1_relat_1 @ B ) =>
% 19.22/19.44           ( r1_tarski @
% 19.22/19.44             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 19.22/19.44  thf('67', plain,
% 19.22/19.44      (![X12 : $i, X13 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X12)
% 19.22/19.44          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X13 @ X12)) @ 
% 19.22/19.44             (k1_relat_1 @ X13))
% 19.22/19.44          | ~ (v1_relat_1 @ X13))),
% 19.22/19.44      inference('cnf', [status(esa)], [t44_relat_1])).
% 19.22/19.44  thf('68', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 19.22/19.44           k1_xboole_0)
% 19.22/19.44          | ~ (v1_relat_1 @ k1_xboole_0)
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['66', '67'])).
% 19.22/19.44  thf('69', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_xboole_0 @ k1_xboole_0)
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 19.22/19.44             k1_xboole_0))),
% 19.22/19.44      inference('sup-', [status(thm)], ['65', '68'])).
% 19.22/19.44  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.22/19.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 19.22/19.44  thf('71', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X0)
% 19.22/19.44          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 19.22/19.44             k1_xboole_0))),
% 19.22/19.44      inference('demod', [status(thm)], ['69', '70'])).
% 19.22/19.44  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 19.22/19.44  thf('72', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 19.22/19.44      inference('cnf', [status(esa)], [t2_xboole_1])).
% 19.22/19.44  thf(d10_xboole_0, axiom,
% 19.22/19.44    (![A:$i,B:$i]:
% 19.22/19.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 19.22/19.44  thf('73', plain,
% 19.22/19.44      (![X1 : $i, X3 : $i]:
% 19.22/19.44         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 19.22/19.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.22/19.44  thf('74', plain,
% 19.22/19.44      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 19.22/19.44      inference('sup-', [status(thm)], ['72', '73'])).
% 19.22/19.44  thf('75', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X0)
% 19.22/19.44          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 19.22/19.44      inference('sup-', [status(thm)], ['71', '74'])).
% 19.22/19.44  thf('76', plain,
% 19.22/19.44      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 19.22/19.44      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 19.22/19.44  thf('77', plain,
% 19.22/19.44      (![X11 : $i]:
% 19.22/19.44         (((k1_relat_1 @ X11) = (k2_relat_1 @ (k4_relat_1 @ X11)))
% 19.22/19.44          | ~ (v1_relat_1 @ X11))),
% 19.22/19.44      inference('cnf', [status(esa)], [t37_relat_1])).
% 19.22/19.44  thf('78', plain,
% 19.22/19.44      (![X9 : $i]:
% 19.22/19.44         (~ (v1_xboole_0 @ (k2_relat_1 @ X9))
% 19.22/19.44          | ~ (v1_relat_1 @ X9)
% 19.22/19.44          | (v1_xboole_0 @ X9))),
% 19.22/19.44      inference('cnf', [status(esa)], [fc9_relat_1])).
% 19.22/19.44  thf('79', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 19.22/19.44          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 19.22/19.44      inference('sup-', [status(thm)], ['77', '78'])).
% 19.22/19.44  thf('80', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X0)
% 19.22/19.44          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 19.22/19.44      inference('sup-', [status(thm)], ['76', '79'])).
% 19.22/19.44  thf('81', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 19.22/19.44          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('simplify', [status(thm)], ['80'])).
% 19.22/19.44  thf('82', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_xboole_0 @ k1_xboole_0)
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 19.22/19.44          | (v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 19.22/19.44      inference('sup-', [status(thm)], ['75', '81'])).
% 19.22/19.44  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.22/19.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 19.22/19.44  thf('84', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 19.22/19.44          | (v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 19.22/19.44      inference('demod', [status(thm)], ['82', '83'])).
% 19.22/19.44  thf('85', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ k1_xboole_0)
% 19.22/19.44          | (v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('sup-', [status(thm)], ['64', '84'])).
% 19.22/19.44  thf('86', plain, ((v1_relat_1 @ k1_xboole_0)),
% 19.22/19.44      inference('demod', [status(thm)], ['50', '51'])).
% 19.22/19.44  thf('87', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X0)
% 19.22/19.44          | (v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('demod', [status(thm)], ['85', '86'])).
% 19.22/19.44  thf('88', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         ((v1_xboole_0 @ (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('simplify', [status(thm)], ['87'])).
% 19.22/19.44  thf('89', plain,
% 19.22/19.44      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 19.22/19.44      inference('sup-', [status(thm)], ['26', '27'])).
% 19.22/19.44  thf('90', plain,
% 19.22/19.44      (![X10 : $i]:
% 19.22/19.44         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 19.22/19.44      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 19.22/19.44  thf('91', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k1_xboole_0) = (X0))
% 19.22/19.44          | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['89', '90'])).
% 19.22/19.44  thf('92', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 19.22/19.44          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 19.22/19.44      inference('sup-', [status(thm)], ['88', '91'])).
% 19.22/19.44  thf('93', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ k1_xboole_0)
% 19.22/19.44          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('sup-', [status(thm)], ['63', '92'])).
% 19.22/19.44  thf('94', plain, ((v1_relat_1 @ k1_xboole_0)),
% 19.22/19.44      inference('demod', [status(thm)], ['50', '51'])).
% 19.22/19.44  thf('95', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X0)
% 19.22/19.44          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('demod', [status(thm)], ['93', '94'])).
% 19.22/19.44  thf('96', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('simplify', [status(thm)], ['95'])).
% 19.22/19.44  thf('97', plain,
% 19.22/19.44      (![X0 : $i, X1 : $i]:
% 19.22/19.44         (((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 19.22/19.44          | ~ (v1_xboole_0 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ X1))),
% 19.22/19.44      inference('sup+', [status(thm)], ['62', '96'])).
% 19.22/19.44  thf('98', plain,
% 19.22/19.44      (![X0 : $i, X1 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_xboole_0 @ X1)
% 19.22/19.44          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))))),
% 19.22/19.44      inference('sup-', [status(thm)], ['61', '97'])).
% 19.22/19.44  thf('99', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_xboole_0 @ k1_xboole_0)
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('sup+', [status(thm)], ['60', '98'])).
% 19.22/19.44  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.22/19.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 19.22/19.44  thf('101', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('demod', [status(thm)], ['99', '100'])).
% 19.22/19.44  thf('102', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X0)
% 19.22/19.44          | ((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 19.22/19.44      inference('simplify', [status(thm)], ['101'])).
% 19.22/19.44  thf('103', plain,
% 19.22/19.44      (![X10 : $i]:
% 19.22/19.44         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 19.22/19.44      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 19.22/19.44  thf('104', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 19.22/19.44      inference('sup+', [status(thm)], ['102', '103'])).
% 19.22/19.44  thf('105', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.22/19.44      inference('demod', [status(thm)], ['54', '55'])).
% 19.22/19.44  thf('106', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 19.22/19.44      inference('demod', [status(thm)], ['104', '105'])).
% 19.22/19.44  thf('107', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ k1_xboole_0)
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 19.22/19.44      inference('sup-', [status(thm)], ['0', '106'])).
% 19.22/19.44  thf('108', plain, ((v1_relat_1 @ k1_xboole_0)),
% 19.22/19.44      inference('demod', [status(thm)], ['50', '51'])).
% 19.22/19.44  thf('109', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (~ (v1_relat_1 @ X0)
% 19.22/19.44          | ~ (v1_relat_1 @ X0)
% 19.22/19.44          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 19.22/19.44      inference('demod', [status(thm)], ['107', '108'])).
% 19.22/19.44  thf('110', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('simplify', [status(thm)], ['109'])).
% 19.22/19.44  thf('111', plain,
% 19.22/19.44      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('cnf', [status(esa)], [l13_xboole_0])).
% 19.22/19.44  thf(t62_relat_1, conjecture,
% 19.22/19.44    (![A:$i]:
% 19.22/19.44     ( ( v1_relat_1 @ A ) =>
% 19.22/19.44       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 19.22/19.44         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 19.22/19.44  thf(zf_stmt_0, negated_conjecture,
% 19.22/19.44    (~( ![A:$i]:
% 19.22/19.44        ( ( v1_relat_1 @ A ) =>
% 19.22/19.44          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 19.22/19.44            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 19.22/19.44    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 19.22/19.44  thf('112', plain,
% 19.22/19.44      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 19.22/19.44        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 19.22/19.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.22/19.44  thf('113', plain,
% 19.22/19.44      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 19.22/19.44         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 19.22/19.44      inference('split', [status(esa)], ['112'])).
% 19.22/19.44  thf('114', plain,
% 19.22/19.44      ((![X0 : $i]:
% 19.22/19.44          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 19.22/19.44         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 19.22/19.44      inference('sup-', [status(thm)], ['111', '113'])).
% 19.22/19.44  thf('115', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 19.22/19.44          | ~ (v1_relat_1 @ X0))),
% 19.22/19.44      inference('simplify', [status(thm)], ['95'])).
% 19.22/19.44  thf('116', plain,
% 19.22/19.44      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('cnf', [status(esa)], [l13_xboole_0])).
% 19.22/19.44  thf('117', plain,
% 19.22/19.44      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 19.22/19.44         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 19.22/19.44      inference('split', [status(esa)], ['112'])).
% 19.22/19.44  thf('118', plain,
% 19.22/19.44      ((![X0 : $i]:
% 19.22/19.44          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 19.22/19.44         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 19.22/19.44      inference('sup-', [status(thm)], ['116', '117'])).
% 19.22/19.44  thf('119', plain,
% 19.22/19.44      (((((k1_xboole_0) != (k1_xboole_0))
% 19.22/19.44         | ~ (v1_relat_1 @ sk_A)
% 19.22/19.44         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 19.22/19.44         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 19.22/19.44      inference('sup-', [status(thm)], ['115', '118'])).
% 19.22/19.44  thf('120', plain, ((v1_relat_1 @ sk_A)),
% 19.22/19.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.22/19.44  thf('121', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.22/19.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 19.22/19.44  thf('122', plain,
% 19.22/19.44      ((((k1_xboole_0) != (k1_xboole_0)))
% 19.22/19.44         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 19.22/19.44      inference('demod', [status(thm)], ['119', '120', '121'])).
% 19.22/19.44  thf('123', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 19.22/19.44      inference('simplify', [status(thm)], ['122'])).
% 19.22/19.44  thf('124', plain,
% 19.22/19.44      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 19.22/19.44       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 19.22/19.44      inference('split', [status(esa)], ['112'])).
% 19.22/19.44  thf('125', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 19.22/19.44      inference('sat_resolution*', [status(thm)], ['123', '124'])).
% 19.22/19.44  thf('126', plain,
% 19.22/19.44      (![X0 : $i]:
% 19.22/19.44         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 19.22/19.44      inference('simpl_trail', [status(thm)], ['114', '125'])).
% 19.22/19.44  thf('127', plain,
% 19.22/19.44      ((((k1_xboole_0) != (k1_xboole_0))
% 19.22/19.44        | ~ (v1_relat_1 @ sk_A)
% 19.22/19.44        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 19.22/19.44      inference('sup-', [status(thm)], ['110', '126'])).
% 19.22/19.44  thf('128', plain, ((v1_relat_1 @ sk_A)),
% 19.22/19.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.22/19.44  thf('129', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.22/19.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 19.22/19.44  thf('130', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 19.22/19.44      inference('demod', [status(thm)], ['127', '128', '129'])).
% 19.22/19.44  thf('131', plain, ($false), inference('simplify', [status(thm)], ['130'])).
% 19.22/19.44  
% 19.22/19.44  % SZS output end Refutation
% 19.22/19.44  
% 19.22/19.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
