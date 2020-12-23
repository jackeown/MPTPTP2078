%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vvdduba57L

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:31 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 290 expanded)
%              Number of leaves         :   22 (  97 expanded)
%              Depth                    :   30
%              Number of atoms          :  724 (1957 expanded)
%              Number of equality atoms :   67 ( 161 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('8',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('12',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['37'])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','39'])).

thf('41',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X12: $i] :
      ( ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('48',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','55'])).

thf('57',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','38'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('61',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('69',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('74',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('80',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['63','80'])).

thf('82',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    $false ),
    inference(simplify,[status(thm)],['85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vvdduba57L
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:46:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.69/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.88  % Solved by: fo/fo7.sh
% 0.69/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.88  % done 712 iterations in 0.417s
% 0.69/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.88  % SZS output start Refutation
% 0.69/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.69/0.88  thf(dt_k5_relat_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.69/0.88       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.69/0.88  thf('0', plain,
% 0.69/0.88      (![X9 : $i, X10 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X9)
% 0.69/0.88          | ~ (v1_relat_1 @ X10)
% 0.69/0.88          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.69/0.88      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.69/0.88  thf(t60_relat_1, axiom,
% 0.69/0.88    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.69/0.88     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.69/0.88  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.88      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.69/0.88  thf(t45_relat_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ A ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( v1_relat_1 @ B ) =>
% 0.69/0.88           ( r1_tarski @
% 0.69/0.88             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.69/0.88  thf('2', plain,
% 0.69/0.88      (![X13 : $i, X14 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X13)
% 0.69/0.88          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X14 @ X13)) @ 
% 0.69/0.88             (k2_relat_1 @ X13))
% 0.69/0.88          | ~ (v1_relat_1 @ X14))),
% 0.69/0.88      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.69/0.88  thf('3', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.69/0.88           k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['1', '2'])).
% 0.69/0.88  thf(t62_relat_1, conjecture,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ A ) =>
% 0.69/0.88       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.69/0.88         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.88    (~( ![A:$i]:
% 0.69/0.88        ( ( v1_relat_1 @ A ) =>
% 0.69/0.88          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.69/0.88            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.69/0.88    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.69/0.88  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(cc1_relat_1, axiom,
% 0.69/0.88    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.69/0.88  thf('5', plain, (![X8 : $i]: ((v1_relat_1 @ X8) | ~ (v1_xboole_0 @ X8))),
% 0.69/0.88      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.69/0.88  thf('6', plain,
% 0.69/0.88      (![X9 : $i, X10 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X9)
% 0.69/0.88          | ~ (v1_relat_1 @ X10)
% 0.69/0.88          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.69/0.88      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.69/0.88  thf('7', plain, (![X8 : $i]: ((v1_relat_1 @ X8) | ~ (v1_xboole_0 @ X8))),
% 0.69/0.88      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.69/0.88  thf('8', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.88      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.69/0.88  thf(t46_relat_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ A ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( v1_relat_1 @ B ) =>
% 0.69/0.88           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.69/0.88             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.69/0.88  thf('9', plain,
% 0.69/0.88      (![X15 : $i, X16 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X15)
% 0.69/0.88          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15)) = (k1_relat_1 @ X16))
% 0.69/0.88          | ~ (r1_tarski @ (k2_relat_1 @ X16) @ (k1_relat_1 @ X15))
% 0.69/0.88          | ~ (v1_relat_1 @ X16))),
% 0.69/0.88      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.69/0.88  thf('10', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.69/0.88              = (k1_relat_1 @ k1_xboole_0))
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['8', '9'])).
% 0.69/0.88  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.69/0.88  thf('11', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.69/0.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.69/0.88  thf('12', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.88      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.69/0.88  thf('13', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.69/0.88  thf('14', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['7', '13'])).
% 0.69/0.88  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.69/0.88  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf('16', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['14', '15'])).
% 0.69/0.88  thf(fc8_relat_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.69/0.88       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.69/0.88  thf('17', plain,
% 0.69/0.88      (![X11 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ (k1_relat_1 @ X11))
% 0.69/0.88          | ~ (v1_relat_1 @ X11)
% 0.69/0.88          | (v1_xboole_0 @ X11))),
% 0.69/0.88      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.69/0.88  thf('18', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['16', '17'])).
% 0.69/0.88  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf('20', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['18', '19'])).
% 0.69/0.88  thf('21', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['6', '20'])).
% 0.69/0.88  thf('22', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['21'])).
% 0.69/0.88  thf('23', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['5', '22'])).
% 0.69/0.88  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf('25', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['23', '24'])).
% 0.69/0.88  thf('26', plain, (![X8 : $i]: ((v1_relat_1 @ X8) | ~ (v1_xboole_0 @ X8))),
% 0.69/0.88      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.69/0.88  thf(l13_xboole_0, axiom,
% 0.69/0.88    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.69/0.88  thf('27', plain,
% 0.69/0.88      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.88  thf('28', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['23', '24'])).
% 0.69/0.88  thf('29', plain,
% 0.69/0.88      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.88  thf('30', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['28', '29'])).
% 0.69/0.88  thf('31', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.69/0.88          | ~ (v1_xboole_0 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['27', '30'])).
% 0.69/0.88  thf('32', plain,
% 0.69/0.88      (![X9 : $i, X10 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X9)
% 0.69/0.88          | ~ (v1_relat_1 @ X10)
% 0.69/0.88          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.69/0.88      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.69/0.88  thf('33', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_xboole_0 @ X1)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['31', '32'])).
% 0.69/0.88  thf('34', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X1)
% 0.69/0.88          | ~ (v1_xboole_0 @ X1)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | (v1_relat_1 @ k1_xboole_0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['33'])).
% 0.69/0.88  thf('35', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ X0)
% 0.69/0.88          | (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1)
% 0.69/0.88          | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['26', '34'])).
% 0.69/0.88  thf('36', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X1)
% 0.69/0.88          | (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['35'])).
% 0.69/0.88  thf('37', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1))),
% 0.69/0.88      inference('sup-', [status(thm)], ['25', '36'])).
% 0.69/0.88  thf('38', plain,
% 0.69/0.88      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.69/0.88      inference('condensation', [status(thm)], ['37'])).
% 0.69/0.88  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.69/0.88      inference('sup-', [status(thm)], ['4', '38'])).
% 0.69/0.88  thf('40', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.69/0.88           k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('demod', [status(thm)], ['3', '39'])).
% 0.69/0.88  thf('41', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.69/0.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.69/0.88  thf(d10_xboole_0, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.69/0.88  thf('42', plain,
% 0.69/0.88      (![X1 : $i, X3 : $i]:
% 0.69/0.88         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.69/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.88  thf('43', plain,
% 0.69/0.88      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['41', '42'])).
% 0.69/0.88  thf('44', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['40', '43'])).
% 0.69/0.88  thf(t21_relat_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ A ) =>
% 0.69/0.88       ( r1_tarski @
% 0.69/0.88         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.69/0.88  thf('45', plain,
% 0.69/0.88      (![X12 : $i]:
% 0.69/0.88         ((r1_tarski @ X12 @ 
% 0.69/0.88           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.69/0.88          | ~ (v1_relat_1 @ X12))),
% 0.69/0.88      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.69/0.88  thf('46', plain,
% 0.69/0.88      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.88  thf(t113_zfmisc_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.69/0.88       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.69/0.88  thf('47', plain,
% 0.69/0.88      (![X6 : $i, X7 : $i]:
% 0.69/0.88         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.69/0.88  thf('48', plain,
% 0.69/0.88      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['47'])).
% 0.69/0.88  thf('49', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['46', '48'])).
% 0.69/0.88  thf('50', plain,
% 0.69/0.88      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['41', '42'])).
% 0.69/0.88  thf('51', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         (~ (r1_tarski @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.69/0.88          | ~ (v1_xboole_0 @ X0)
% 0.69/0.88          | ((X2) = (k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['49', '50'])).
% 0.69/0.88  thf('52', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ((X0) = (k1_xboole_0))
% 0.69/0.88          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['45', '51'])).
% 0.69/0.88  thf('53', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.69/0.88          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['44', '52'])).
% 0.69/0.88  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf('55', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.69/0.88          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['53', '54'])).
% 0.69/0.88  thf('56', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['0', '55'])).
% 0.69/0.88  thf('57', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.69/0.88      inference('sup-', [status(thm)], ['4', '38'])).
% 0.69/0.88  thf('58', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('demod', [status(thm)], ['56', '57'])).
% 0.69/0.88  thf('59', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['58'])).
% 0.69/0.88  thf('60', plain,
% 0.69/0.88      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.88  thf('61', plain,
% 0.69/0.88      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.69/0.88        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('62', plain,
% 0.69/0.88      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.69/0.88         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.69/0.88      inference('split', [status(esa)], ['61'])).
% 0.69/0.88  thf('63', plain,
% 0.69/0.88      ((![X0 : $i]:
% 0.69/0.88          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.69/0.88         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['60', '62'])).
% 0.69/0.88  thf('64', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['23', '24'])).
% 0.69/0.88  thf('65', plain,
% 0.69/0.88      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.88  thf('66', plain,
% 0.69/0.88      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.88  thf('67', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['65', '66'])).
% 0.69/0.88  thf('68', plain,
% 0.69/0.88      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.88  thf('69', plain,
% 0.69/0.88      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.69/0.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('split', [status(esa)], ['61'])).
% 0.69/0.88  thf('70', plain,
% 0.69/0.88      ((![X0 : $i]:
% 0.69/0.88          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.69/0.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['68', '69'])).
% 0.69/0.88  thf('71', plain,
% 0.69/0.88      ((![X0 : $i, X1 : $i]:
% 0.69/0.88          (((X0) != (k1_xboole_0))
% 0.69/0.88           | ~ (v1_xboole_0 @ X0)
% 0.69/0.88           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.69/0.88           | ~ (v1_xboole_0 @ X1)))
% 0.69/0.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['67', '70'])).
% 0.69/0.88  thf('72', plain,
% 0.69/0.88      ((![X1 : $i]:
% 0.69/0.88          (~ (v1_xboole_0 @ X1)
% 0.69/0.88           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.69/0.88           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.69/0.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('simplify', [status(thm)], ['71'])).
% 0.69/0.88  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf('74', plain,
% 0.69/0.88      ((![X1 : $i]:
% 0.69/0.88          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.69/0.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('simplify_reflect+', [status(thm)], ['72', '73'])).
% 0.69/0.88  thf('75', plain,
% 0.69/0.88      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.69/0.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['64', '74'])).
% 0.69/0.88  thf('76', plain, ((v1_relat_1 @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf('78', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.69/0.88  thf('79', plain,
% 0.69/0.88      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.69/0.88       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.69/0.88      inference('split', [status(esa)], ['61'])).
% 0.69/0.88  thf('80', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.69/0.88      inference('sat_resolution*', [status(thm)], ['78', '79'])).
% 0.69/0.88  thf('81', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('simpl_trail', [status(thm)], ['63', '80'])).
% 0.69/0.88  thf('82', plain,
% 0.69/0.88      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.88        | ~ (v1_relat_1 @ sk_A)
% 0.69/0.88        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['59', '81'])).
% 0.69/0.88  thf('83', plain, ((v1_relat_1 @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf('85', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.69/0.88      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.69/0.88  thf('86', plain, ($false), inference('simplify', [status(thm)], ['85'])).
% 0.69/0.88  
% 0.69/0.88  % SZS output end Refutation
% 0.69/0.88  
% 0.69/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
