%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ThMlkZ4QpI

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:30 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 185 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :   25
%              Number of atoms          :  753 (1226 expanded)
%              Number of equality atoms :   63 ( 115 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X14 @ X15 ) )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('6',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( r1_tarski @ X11 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

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

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('22',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('29',plain,
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

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k2_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','48'])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('66',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('74',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['66'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['66'])).

thf('85',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['68','85'])).

thf('87',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    $false ),
    inference(simplify,[status(thm)],['90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ThMlkZ4QpI
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.58/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.81  % Solved by: fo/fo7.sh
% 0.58/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.81  % done 563 iterations in 0.361s
% 0.58/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.81  % SZS output start Refutation
% 0.58/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.81  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.58/0.81  thf(dt_k5_relat_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.58/0.81       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.58/0.81  thf('0', plain,
% 0.58/0.81      (![X8 : $i, X9 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X8)
% 0.58/0.81          | ~ (v1_relat_1 @ X9)
% 0.58/0.81          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.58/0.81      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.58/0.81  thf(cc1_relat_1, axiom,
% 0.58/0.81    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.58/0.81  thf('1', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.58/0.81      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.58/0.81  thf(t60_relat_1, axiom,
% 0.58/0.81    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.58/0.81     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.58/0.81  thf('2', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.81  thf(t47_relat_1, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( v1_relat_1 @ A ) =>
% 0.58/0.81       ( ![B:$i]:
% 0.58/0.81         ( ( v1_relat_1 @ B ) =>
% 0.58/0.81           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.58/0.81             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.58/0.81  thf('3', plain,
% 0.58/0.81      (![X14 : $i, X15 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X14)
% 0.58/0.81          | ((k2_relat_1 @ (k5_relat_1 @ X14 @ X15)) = (k2_relat_1 @ X15))
% 0.58/0.81          | ~ (r1_tarski @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X14))
% 0.58/0.81          | ~ (v1_relat_1 @ X15))),
% 0.58/0.81      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.58/0.81  thf('4', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.58/0.81          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.81          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.58/0.81              = (k2_relat_1 @ k1_xboole_0))
% 0.58/0.81          | ~ (v1_relat_1 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.81  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.58/0.81  thf('5', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.58/0.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.81  thf('6', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.81  thf('7', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.81          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.58/0.81          | ~ (v1_relat_1 @ X0))),
% 0.58/0.81      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.58/0.81  thf('8', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_relat_1 @ X0)
% 0.58/0.81          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['1', '7'])).
% 0.58/0.81  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.58/0.81  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.81  thf('10', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X0)
% 0.58/0.81          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['8', '9'])).
% 0.58/0.81  thf(fc3_zfmisc_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.58/0.81  thf('11', plain,
% 0.58/0.81      (![X5 : $i, X6 : $i]:
% 0.58/0.81         ((v1_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6)) | ~ (v1_xboole_0 @ X6))),
% 0.58/0.81      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.58/0.81  thf(l13_xboole_0, axiom,
% 0.58/0.81    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.58/0.81  thf('12', plain,
% 0.58/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.81  thf('13', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['11', '12'])).
% 0.58/0.81  thf(t21_relat_1, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( v1_relat_1 @ A ) =>
% 0.58/0.81       ( r1_tarski @
% 0.58/0.81         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.58/0.81  thf('14', plain,
% 0.58/0.81      (![X11 : $i]:
% 0.58/0.81         ((r1_tarski @ X11 @ 
% 0.58/0.81           (k2_zfmisc_1 @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X11)))
% 0.58/0.81          | ~ (v1_relat_1 @ X11))),
% 0.58/0.81      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.58/0.81  thf('15', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r1_tarski @ X0 @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.58/0.81          | ~ (v1_relat_1 @ X0))),
% 0.58/0.81      inference('sup+', [status(thm)], ['13', '14'])).
% 0.58/0.81  thf('16', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_relat_1 @ X0)
% 0.58/0.81          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.58/0.81          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['10', '15'])).
% 0.58/0.81  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.81  thf('18', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X0)
% 0.58/0.81          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.58/0.81          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.58/0.81      inference('demod', [status(thm)], ['16', '17'])).
% 0.58/0.81  thf('19', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_relat_1 @ X0)
% 0.58/0.81          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_relat_1 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['0', '18'])).
% 0.58/0.81  thf(t62_relat_1, conjecture,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( v1_relat_1 @ A ) =>
% 0.58/0.81       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.58/0.81         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.81    (~( ![A:$i]:
% 0.58/0.81        ( ( v1_relat_1 @ A ) =>
% 0.58/0.81          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.58/0.81            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.58/0.81    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.58/0.81  thf('20', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('21', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.81  thf('22', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.58/0.81      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.58/0.81  thf('23', plain,
% 0.58/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.81  thf('24', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.81  thf('25', plain,
% 0.58/0.81      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.81      inference('sup+', [status(thm)], ['23', '24'])).
% 0.58/0.81  thf('26', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.58/0.81      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.58/0.81  thf('27', plain,
% 0.58/0.81      (![X8 : $i, X9 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X8)
% 0.58/0.81          | ~ (v1_relat_1 @ X9)
% 0.58/0.81          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.58/0.81      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.58/0.81  thf('28', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.58/0.81      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.58/0.81  thf('29', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.81  thf(t46_relat_1, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( v1_relat_1 @ A ) =>
% 0.58/0.81       ( ![B:$i]:
% 0.58/0.81         ( ( v1_relat_1 @ B ) =>
% 0.58/0.81           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.58/0.81             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.58/0.81  thf('30', plain,
% 0.58/0.81      (![X12 : $i, X13 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X12)
% 0.58/0.81          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12)) = (k1_relat_1 @ X13))
% 0.58/0.81          | ~ (r1_tarski @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X12))
% 0.58/0.81          | ~ (v1_relat_1 @ X13))),
% 0.58/0.81      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.58/0.81  thf('31', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.58/0.81          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.81          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.58/0.81              = (k1_relat_1 @ k1_xboole_0))
% 0.58/0.81          | ~ (v1_relat_1 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.81  thf('32', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.58/0.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.81  thf('33', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.81  thf('34', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.81          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.58/0.81          | ~ (v1_relat_1 @ X0))),
% 0.58/0.81      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.58/0.81  thf('35', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_relat_1 @ X0)
% 0.58/0.81          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['28', '34'])).
% 0.58/0.81  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.81  thf('37', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X0)
% 0.58/0.81          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['35', '36'])).
% 0.58/0.81  thf(fc8_relat_1, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.58/0.81       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.58/0.81  thf('38', plain,
% 0.58/0.81      (![X10 : $i]:
% 0.58/0.81         (~ (v1_xboole_0 @ (k1_relat_1 @ X10))
% 0.58/0.81          | ~ (v1_relat_1 @ X10)
% 0.58/0.81          | (v1_xboole_0 @ X10))),
% 0.58/0.81      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.58/0.81  thf('39', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_relat_1 @ X0)
% 0.58/0.81          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.58/0.81          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['37', '38'])).
% 0.58/0.81  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.81  thf('41', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X0)
% 0.58/0.81          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.58/0.81          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['39', '40'])).
% 0.58/0.81  thf('42', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X0)
% 0.58/0.81          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.81          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.58/0.81          | ~ (v1_relat_1 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['27', '41'])).
% 0.58/0.81  thf('43', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.58/0.81          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_relat_1 @ X0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['42'])).
% 0.58/0.81  thf('44', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_relat_1 @ X0)
% 0.58/0.81          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['26', '43'])).
% 0.58/0.81  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.81  thf('46', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['44', '45'])).
% 0.58/0.81  thf('47', plain,
% 0.58/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.81  thf('48', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X0)
% 0.58/0.81          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.81  thf('49', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (((k5_relat_1 @ (k2_relat_1 @ X0) @ X1) = (k1_xboole_0))
% 0.58/0.81          | ~ (v1_xboole_0 @ X0)
% 0.58/0.81          | ~ (v1_relat_1 @ X1))),
% 0.58/0.81      inference('sup+', [status(thm)], ['25', '48'])).
% 0.58/0.81  thf('50', plain,
% 0.58/0.81      (![X8 : $i, X9 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X8)
% 0.58/0.81          | ~ (v1_relat_1 @ X9)
% 0.58/0.81          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.58/0.81      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.58/0.81  thf('51', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((v1_relat_1 @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_relat_1 @ X0)
% 0.58/0.81          | ~ (v1_xboole_0 @ X1)
% 0.58/0.81          | ~ (v1_relat_1 @ X0)
% 0.58/0.81          | ~ (v1_relat_1 @ (k2_relat_1 @ X1)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['49', '50'])).
% 0.58/0.81  thf('52', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ (k2_relat_1 @ X1))
% 0.58/0.81          | ~ (v1_xboole_0 @ X1)
% 0.58/0.81          | ~ (v1_relat_1 @ X0)
% 0.58/0.81          | (v1_relat_1 @ k1_xboole_0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['51'])).
% 0.58/0.81  thf('53', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.58/0.81          | (v1_relat_1 @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_relat_1 @ X1)
% 0.58/0.81          | ~ (v1_xboole_0 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['22', '52'])).
% 0.58/0.81  thf('54', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_relat_1 @ X0)
% 0.58/0.81          | (v1_relat_1 @ k1_xboole_0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['21', '53'])).
% 0.58/0.81  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.81  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.81  thf('57', plain,
% 0.58/0.81      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.58/0.81      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.58/0.81  thf('58', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.58/0.81      inference('sup-', [status(thm)], ['20', '57'])).
% 0.58/0.81  thf('59', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X0)
% 0.58/0.81          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_relat_1 @ X0))),
% 0.58/0.81      inference('demod', [status(thm)], ['19', '58'])).
% 0.58/0.81  thf('60', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_relat_1 @ X0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['59'])).
% 0.58/0.81  thf('61', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.58/0.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.81  thf(d10_xboole_0, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.81  thf('62', plain,
% 0.58/0.81      (![X1 : $i, X3 : $i]:
% 0.58/0.81         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.58/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.81  thf('63', plain,
% 0.58/0.81      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['61', '62'])).
% 0.58/0.81  thf('64', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X0)
% 0.58/0.81          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['60', '63'])).
% 0.58/0.81  thf('65', plain,
% 0.58/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.81  thf('66', plain,
% 0.58/0.81      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.58/0.81        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('67', plain,
% 0.58/0.81      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.58/0.81         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.58/0.81      inference('split', [status(esa)], ['66'])).
% 0.58/0.81  thf('68', plain,
% 0.58/0.81      ((![X0 : $i]:
% 0.58/0.81          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.58/0.81         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['65', '67'])).
% 0.58/0.81  thf('69', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['44', '45'])).
% 0.58/0.81  thf('70', plain,
% 0.58/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.81  thf('71', plain,
% 0.58/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.81  thf('72', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.81      inference('sup+', [status(thm)], ['70', '71'])).
% 0.58/0.81  thf('73', plain,
% 0.58/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.81  thf('74', plain,
% 0.58/0.81      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.58/0.81         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.58/0.81      inference('split', [status(esa)], ['66'])).
% 0.58/0.81  thf('75', plain,
% 0.58/0.81      ((![X0 : $i]:
% 0.58/0.81          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.58/0.81         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['73', '74'])).
% 0.58/0.81  thf('76', plain,
% 0.58/0.81      ((![X0 : $i, X1 : $i]:
% 0.58/0.81          (((X0) != (k1_xboole_0))
% 0.58/0.81           | ~ (v1_xboole_0 @ X0)
% 0.58/0.81           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.58/0.81           | ~ (v1_xboole_0 @ X1)))
% 0.58/0.81         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['72', '75'])).
% 0.58/0.81  thf('77', plain,
% 0.58/0.81      ((![X1 : $i]:
% 0.58/0.81          (~ (v1_xboole_0 @ X1)
% 0.58/0.81           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.58/0.81           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.58/0.81         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.58/0.81      inference('simplify', [status(thm)], ['76'])).
% 0.58/0.81  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.81  thf('79', plain,
% 0.58/0.81      ((![X1 : $i]:
% 0.58/0.81          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.58/0.81         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.58/0.81      inference('simplify_reflect+', [status(thm)], ['77', '78'])).
% 0.58/0.81  thf('80', plain,
% 0.58/0.81      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.58/0.81         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['69', '79'])).
% 0.58/0.81  thf('81', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.81  thf('83', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.58/0.81  thf('84', plain,
% 0.58/0.81      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.58/0.81       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.58/0.81      inference('split', [status(esa)], ['66'])).
% 0.58/0.81  thf('85', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.58/0.81      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.58/0.81  thf('86', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.81      inference('simpl_trail', [status(thm)], ['68', '85'])).
% 0.58/0.81  thf('87', plain,
% 0.58/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.81        | ~ (v1_relat_1 @ sk_A)
% 0.58/0.81        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['64', '86'])).
% 0.58/0.81  thf('88', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.81  thf('90', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.58/0.81      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.58/0.81  thf('91', plain, ($false), inference('simplify', [status(thm)], ['90'])).
% 0.58/0.81  
% 0.58/0.81  % SZS output end Refutation
% 0.58/0.81  
% 0.58/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
