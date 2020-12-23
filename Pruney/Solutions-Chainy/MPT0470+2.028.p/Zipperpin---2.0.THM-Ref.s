%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mPDjLjK3jX

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:30 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 200 expanded)
%              Number of leaves         :   22 (  69 expanded)
%              Depth                    :   28
%              Number of atoms          :  753 (1333 expanded)
%              Number of equality atoms :   63 ( 122 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,
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

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
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
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
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
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

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
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i] :
      ( ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

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

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('27',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('29',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('30',plain,
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

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X12: $i] :
      ( ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','55'])).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['63'])).

thf('65',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','64'])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('73',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('78',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['73'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['73'])).

thf('86',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['75','86'])).

thf('88',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    $false ),
    inference(simplify,[status(thm)],['91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mPDjLjK3jX
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 464 iterations in 0.318s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.79  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.59/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.79  thf(dt_k5_relat_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.59/0.79       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.59/0.79  thf('0', plain,
% 0.59/0.79      (![X10 : $i, X11 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X10)
% 0.59/0.79          | ~ (v1_relat_1 @ X11)
% 0.59/0.79          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.59/0.79  thf(cc1_relat_1, axiom,
% 0.59/0.79    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.59/0.79  thf('1', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.59/0.79  thf(t60_relat_1, axiom,
% 0.59/0.79    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.59/0.79     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.59/0.79  thf('2', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.79      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.59/0.79  thf(t46_relat_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ A ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( v1_relat_1 @ B ) =>
% 0.59/0.79           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.59/0.79             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      (![X13 : $i, X14 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X13)
% 0.59/0.79          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13)) = (k1_relat_1 @ X14))
% 0.59/0.79          | ~ (r1_tarski @ (k2_relat_1 @ X14) @ (k1_relat_1 @ X13))
% 0.59/0.79          | ~ (v1_relat_1 @ X14))),
% 0.59/0.79      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.59/0.79          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.59/0.79          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.59/0.79              = (k1_relat_1 @ k1_xboole_0))
% 0.59/0.79          | ~ (v1_relat_1 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.79  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.59/0.79  thf('5', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.59/0.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.79  thf('6', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.79      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ k1_xboole_0)
% 0.59/0.79          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.59/0.79          | ~ (v1_relat_1 @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_relat_1 @ X0)
% 0.59/0.79          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['1', '7'])).
% 0.59/0.79  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.59/0.79  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.59/0.79      inference('demod', [status(thm)], ['8', '9'])).
% 0.59/0.79  thf(fc4_zfmisc_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X7 : $i, X8 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ X7) | (v1_xboole_0 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.59/0.79  thf(l13_xboole_0, axiom,
% 0.59/0.79    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.79  thf(t21_relat_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ A ) =>
% 0.59/0.79       ( r1_tarski @
% 0.59/0.79         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.59/0.79  thf('14', plain,
% 0.59/0.79      (![X12 : $i]:
% 0.59/0.79         ((r1_tarski @ X12 @ 
% 0.59/0.79           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.59/0.79          | ~ (v1_relat_1 @ X12))),
% 0.59/0.79      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((r1_tarski @ X0 @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.59/0.79          | ~ (v1_relat_1 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_relat_1 @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.59/0.79          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['10', '15'])).
% 0.59/0.79  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.59/0.79          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.59/0.79      inference('demod', [status(thm)], ['16', '17'])).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.59/0.79          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_relat_1 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['0', '18'])).
% 0.59/0.79  thf('20', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.79      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.79  thf('22', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.79      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.59/0.79  thf('23', plain,
% 0.59/0.79      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.79  thf(t62_relat_1, conjecture,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ A ) =>
% 0.59/0.79       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.59/0.79         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i]:
% 0.59/0.79        ( ( v1_relat_1 @ A ) =>
% 0.59/0.79          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.59/0.79            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.59/0.79  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('25', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.59/0.79  thf('26', plain,
% 0.59/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.79  thf('27', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.59/0.79  thf('28', plain,
% 0.59/0.79      (![X10 : $i, X11 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X10)
% 0.59/0.79          | ~ (v1_relat_1 @ X11)
% 0.59/0.79          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.59/0.79  thf('29', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.59/0.79  thf('30', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.79      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.59/0.79  thf(t47_relat_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ A ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( v1_relat_1 @ B ) =>
% 0.59/0.79           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.59/0.79             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.79  thf('31', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X15)
% 0.59/0.79          | ((k2_relat_1 @ (k5_relat_1 @ X15 @ X16)) = (k2_relat_1 @ X16))
% 0.59/0.79          | ~ (r1_tarski @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X15))
% 0.59/0.79          | ~ (v1_relat_1 @ X16))),
% 0.59/0.79      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.59/0.79  thf('32', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.59/0.79          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.59/0.79          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.59/0.79              = (k2_relat_1 @ k1_xboole_0))
% 0.59/0.79          | ~ (v1_relat_1 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.79  thf('33', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.59/0.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.79  thf('34', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.79      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.59/0.79  thf('35', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ k1_xboole_0)
% 0.59/0.79          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.59/0.79          | ~ (v1_relat_1 @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.59/0.79  thf('36', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_relat_1 @ X0)
% 0.59/0.79          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['29', '35'])).
% 0.59/0.79  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.79  thf('38', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.59/0.79      inference('demod', [status(thm)], ['36', '37'])).
% 0.59/0.79  thf(fc3_zfmisc_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.59/0.79  thf('39', plain,
% 0.59/0.79      (![X5 : $i, X6 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6)) | ~ (v1_xboole_0 @ X6))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.59/0.79  thf('40', plain,
% 0.59/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.79  thf('41', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.79  thf('42', plain,
% 0.59/0.79      (![X12 : $i]:
% 0.59/0.79         ((r1_tarski @ X12 @ 
% 0.59/0.79           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.59/0.79          | ~ (v1_relat_1 @ X12))),
% 0.59/0.79      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.59/0.79  thf('43', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((r1_tarski @ X0 @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.59/0.79          | ~ (v1_relat_1 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['41', '42'])).
% 0.59/0.79  thf('44', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_relat_1 @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.59/0.79          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['38', '43'])).
% 0.59/0.79  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.79  thf('46', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.59/0.79          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.59/0.79      inference('demod', [status(thm)], ['44', '45'])).
% 0.59/0.79  thf('47', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_relat_1 @ X0)
% 0.59/0.79          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_relat_1 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['28', '46'])).
% 0.59/0.79  thf('48', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_relat_1 @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.59/0.79      inference('simplify', [status(thm)], ['47'])).
% 0.59/0.79  thf('49', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_relat_1 @ X0)
% 0.59/0.79          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['27', '48'])).
% 0.59/0.79  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.79  thf('51', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.59/0.79      inference('demod', [status(thm)], ['49', '50'])).
% 0.59/0.79  thf('52', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.59/0.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.79  thf(d10_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.79  thf('53', plain,
% 0.59/0.79      (![X1 : $i, X3 : $i]:
% 0.59/0.79         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.59/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.79  thf('54', plain,
% 0.59/0.79      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['52', '53'])).
% 0.59/0.79  thf('55', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['51', '54'])).
% 0.59/0.79  thf('56', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.59/0.79          | ~ (v1_xboole_0 @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ X1))),
% 0.59/0.79      inference('sup+', [status(thm)], ['26', '55'])).
% 0.59/0.79  thf('57', plain,
% 0.59/0.79      (![X10 : $i, X11 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X10)
% 0.59/0.79          | ~ (v1_relat_1 @ X11)
% 0.59/0.79          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.59/0.79  thf('58', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((v1_relat_1 @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_relat_1 @ X1)
% 0.59/0.79          | ~ (v1_xboole_0 @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ X1))),
% 0.59/0.79      inference('sup+', [status(thm)], ['56', '57'])).
% 0.59/0.79  thf('59', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | ~ (v1_xboole_0 @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ X1)
% 0.59/0.79          | (v1_relat_1 @ k1_xboole_0))),
% 0.59/0.79      inference('simplify', [status(thm)], ['58'])).
% 0.59/0.79  thf('60', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ X0)
% 0.59/0.79          | (v1_relat_1 @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_relat_1 @ X1)
% 0.59/0.79          | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['25', '59'])).
% 0.59/0.79  thf('61', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X1)
% 0.59/0.79          | (v1_relat_1 @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('simplify', [status(thm)], ['60'])).
% 0.59/0.79  thf('62', plain,
% 0.59/0.79      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['24', '61'])).
% 0.59/0.79  thf('63', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((v1_relat_1 @ (k2_relat_1 @ X0))
% 0.59/0.79          | ~ (v1_xboole_0 @ X0)
% 0.59/0.79          | ~ (v1_xboole_0 @ X1))),
% 0.59/0.79      inference('sup+', [status(thm)], ['23', '62'])).
% 0.59/0.79  thf('64', plain,
% 0.59/0.79      (![X0 : $i]: ((v1_relat_1 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('condensation', [status(thm)], ['63'])).
% 0.59/0.79  thf('65', plain,
% 0.59/0.79      (((v1_relat_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['20', '64'])).
% 0.59/0.79  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.79  thf('67', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.59/0.79      inference('demod', [status(thm)], ['65', '66'])).
% 0.59/0.79  thf('68', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_relat_1 @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['19', '67'])).
% 0.59/0.79  thf('69', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.59/0.79          | ~ (v1_relat_1 @ X0))),
% 0.59/0.79      inference('simplify', [status(thm)], ['68'])).
% 0.59/0.79  thf('70', plain,
% 0.59/0.79      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['52', '53'])).
% 0.59/0.79  thf('71', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['69', '70'])).
% 0.59/0.79  thf('72', plain,
% 0.59/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.79  thf('73', plain,
% 0.59/0.79      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.59/0.79        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('74', plain,
% 0.59/0.79      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.59/0.79         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.59/0.79      inference('split', [status(esa)], ['73'])).
% 0.59/0.79  thf('75', plain,
% 0.59/0.79      ((![X0 : $i]:
% 0.59/0.79          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.59/0.79         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['72', '74'])).
% 0.59/0.79  thf('76', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['51', '54'])).
% 0.59/0.79  thf('77', plain,
% 0.59/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.79  thf('78', plain,
% 0.59/0.79      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.59/0.79         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.59/0.79      inference('split', [status(esa)], ['73'])).
% 0.59/0.79  thf('79', plain,
% 0.59/0.79      ((![X0 : $i]:
% 0.59/0.79          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.59/0.79         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['77', '78'])).
% 0.59/0.79  thf('80', plain,
% 0.59/0.79      (((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.79         | ~ (v1_relat_1 @ sk_A)
% 0.59/0.79         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.59/0.79         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['76', '79'])).
% 0.59/0.79  thf('81', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.79  thf('83', plain,
% 0.59/0.79      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.59/0.79         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.59/0.79      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.59/0.79  thf('84', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['83'])).
% 0.59/0.79  thf('85', plain,
% 0.59/0.79      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 0.59/0.79       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.59/0.79      inference('split', [status(esa)], ['73'])).
% 0.59/0.79  thf('86', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.59/0.79      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 0.59/0.79  thf('87', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('simpl_trail', [status(thm)], ['75', '86'])).
% 0.59/0.79  thf('88', plain,
% 0.59/0.79      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.79        | ~ (v1_relat_1 @ sk_A)
% 0.59/0.79        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['71', '87'])).
% 0.59/0.79  thf('89', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.79  thf('91', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.59/0.79      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.59/0.79  thf('92', plain, ($false), inference('simplify', [status(thm)], ['91'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.66/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
