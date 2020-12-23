%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hAq1TYAZ5e

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:30 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 186 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :   25
%              Number of atoms          :  735 (1221 expanded)
%              Number of equality atoms :   58 ( 110 expanded)
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
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X11: $i] :
      ( ( r1_tarski @ X11 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','19'])).

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

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('23',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('29',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('30',plain,
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

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k1_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','49'])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('65',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('73',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('84',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['67','84'])).

thf('86',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('89',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    $false ),
    inference(simplify,[status(thm)],['89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hAq1TYAZ5e
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.73  % Solved by: fo/fo7.sh
% 0.50/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.73  % done 418 iterations in 0.274s
% 0.50/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.73  % SZS output start Refutation
% 0.50/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.50/0.73  thf(dt_k5_relat_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.50/0.73       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.50/0.73  thf('0', plain,
% 0.50/0.73      (![X8 : $i, X9 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X8)
% 0.50/0.73          | ~ (v1_relat_1 @ X9)
% 0.50/0.73          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.50/0.73      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.50/0.73  thf(cc1_relat_1, axiom,
% 0.50/0.73    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.50/0.73  thf('1', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.50/0.73      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.50/0.73  thf(t60_relat_1, axiom,
% 0.50/0.73    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.50/0.73     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.50/0.73  thf('2', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.73      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.50/0.73  thf(t45_relat_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v1_relat_1 @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( v1_relat_1 @ B ) =>
% 0.50/0.73           ( r1_tarski @
% 0.50/0.73             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.50/0.73  thf('3', plain,
% 0.50/0.73      (![X12 : $i, X13 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X12)
% 0.50/0.73          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X13 @ X12)) @ 
% 0.50/0.73             (k2_relat_1 @ X12))
% 0.50/0.73          | ~ (v1_relat_1 @ X13))),
% 0.50/0.73      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.50/0.73  thf('4', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.50/0.73           k1_xboole_0)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.50/0.73      inference('sup+', [status(thm)], ['2', '3'])).
% 0.50/0.73  thf('5', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.50/0.73             k1_xboole_0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['1', '4'])).
% 0.50/0.73  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.50/0.73  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.50/0.73  thf('7', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0)
% 0.50/0.73          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.50/0.73             k1_xboole_0))),
% 0.50/0.73      inference('demod', [status(thm)], ['5', '6'])).
% 0.50/0.73  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.50/0.73  thf('8', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.50/0.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.73  thf(d10_xboole_0, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.73  thf('9', plain,
% 0.50/0.73      (![X1 : $i, X3 : $i]:
% 0.50/0.73         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.50/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.73  thf('10', plain,
% 0.50/0.73      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.73  thf('11', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0)
% 0.50/0.73          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['7', '10'])).
% 0.50/0.73  thf(fc3_zfmisc_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.50/0.73  thf('12', plain,
% 0.50/0.73      (![X5 : $i, X6 : $i]:
% 0.50/0.73         ((v1_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6)) | ~ (v1_xboole_0 @ X6))),
% 0.50/0.73      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.50/0.73  thf(l13_xboole_0, axiom,
% 0.50/0.73    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.50/0.73  thf('13', plain,
% 0.50/0.73      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.50/0.73  thf('14', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['12', '13'])).
% 0.50/0.73  thf(t21_relat_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v1_relat_1 @ A ) =>
% 0.50/0.73       ( r1_tarski @
% 0.50/0.73         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.50/0.73  thf('15', plain,
% 0.50/0.73      (![X11 : $i]:
% 0.50/0.73         ((r1_tarski @ X11 @ 
% 0.50/0.73           (k2_zfmisc_1 @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X11)))
% 0.50/0.73          | ~ (v1_relat_1 @ X11))),
% 0.50/0.73      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.50/0.73  thf('16', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((r1_tarski @ X0 @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.50/0.73          | ~ (v1_relat_1 @ X0))),
% 0.50/0.73      inference('sup+', [status(thm)], ['14', '15'])).
% 0.50/0.73  thf('17', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.50/0.73          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['11', '16'])).
% 0.50/0.73  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.50/0.73  thf('19', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0)
% 0.50/0.73          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.50/0.73          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.50/0.73      inference('demod', [status(thm)], ['17', '18'])).
% 0.50/0.73  thf('20', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_relat_1 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['0', '19'])).
% 0.50/0.73  thf(t62_relat_1, conjecture,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v1_relat_1 @ A ) =>
% 0.50/0.73       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.50/0.73         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.50/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.73    (~( ![A:$i]:
% 0.50/0.73        ( ( v1_relat_1 @ A ) =>
% 0.50/0.73          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.50/0.73            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.50/0.73    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.50/0.73  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('22', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.73      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.50/0.73  thf('23', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.50/0.73      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.50/0.73  thf('24', plain,
% 0.50/0.73      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.50/0.73  thf('25', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.73      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.50/0.73  thf('26', plain,
% 0.50/0.73      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.73      inference('sup+', [status(thm)], ['24', '25'])).
% 0.50/0.73  thf('27', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.50/0.73      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.50/0.73  thf('28', plain,
% 0.50/0.73      (![X8 : $i, X9 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X8)
% 0.50/0.73          | ~ (v1_relat_1 @ X9)
% 0.50/0.73          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.50/0.73      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.50/0.73  thf('29', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.50/0.73      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.50/0.73  thf('30', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.73      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.50/0.73  thf(t46_relat_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v1_relat_1 @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( v1_relat_1 @ B ) =>
% 0.50/0.73           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.50/0.73             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.50/0.73  thf('31', plain,
% 0.50/0.73      (![X14 : $i, X15 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X14)
% 0.50/0.73          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14)) = (k1_relat_1 @ X15))
% 0.50/0.73          | ~ (r1_tarski @ (k2_relat_1 @ X15) @ (k1_relat_1 @ X14))
% 0.50/0.73          | ~ (v1_relat_1 @ X15))),
% 0.50/0.73      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.50/0.73  thf('32', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.50/0.73          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.50/0.73          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.50/0.73              = (k1_relat_1 @ k1_xboole_0))
% 0.50/0.73          | ~ (v1_relat_1 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.50/0.73  thf('33', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.50/0.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.73  thf('34', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.73      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.50/0.73  thf('35', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ k1_xboole_0)
% 0.50/0.73          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.50/0.73          | ~ (v1_relat_1 @ X0))),
% 0.50/0.73      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.50/0.73  thf('36', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['29', '35'])).
% 0.50/0.73  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.50/0.73  thf('38', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0)
% 0.50/0.73          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.50/0.73      inference('demod', [status(thm)], ['36', '37'])).
% 0.50/0.73  thf(fc8_relat_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.50/0.73       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.50/0.73  thf('39', plain,
% 0.50/0.73      (![X10 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ (k1_relat_1 @ X10))
% 0.50/0.73          | ~ (v1_relat_1 @ X10)
% 0.50/0.73          | (v1_xboole_0 @ X10))),
% 0.50/0.73      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.50/0.73  thf('40', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.50/0.73          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['38', '39'])).
% 0.50/0.73  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.50/0.73  thf('42', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0)
% 0.50/0.73          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.50/0.73          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.50/0.73      inference('demod', [status(thm)], ['40', '41'])).
% 0.50/0.73  thf('43', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0)
% 0.50/0.73          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.50/0.73          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.50/0.73          | ~ (v1_relat_1 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['28', '42'])).
% 0.50/0.73  thf('44', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.50/0.73          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_relat_1 @ X0))),
% 0.50/0.73      inference('simplify', [status(thm)], ['43'])).
% 0.50/0.73  thf('45', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['27', '44'])).
% 0.50/0.73  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.50/0.73  thf('47', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.50/0.73      inference('demod', [status(thm)], ['45', '46'])).
% 0.50/0.73  thf('48', plain,
% 0.50/0.73      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.50/0.73  thf('49', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0)
% 0.50/0.73          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['47', '48'])).
% 0.50/0.73  thf('50', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (((k5_relat_1 @ (k1_relat_1 @ X0) @ X1) = (k1_xboole_0))
% 0.50/0.73          | ~ (v1_xboole_0 @ X0)
% 0.50/0.73          | ~ (v1_relat_1 @ X1))),
% 0.50/0.73      inference('sup+', [status(thm)], ['26', '49'])).
% 0.50/0.73  thf('51', plain,
% 0.50/0.73      (![X8 : $i, X9 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X8)
% 0.50/0.73          | ~ (v1_relat_1 @ X9)
% 0.50/0.73          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.50/0.73      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.50/0.73  thf('52', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         ((v1_relat_1 @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | ~ (v1_xboole_0 @ X1)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | ~ (v1_relat_1 @ (k1_relat_1 @ X1)))),
% 0.50/0.73      inference('sup+', [status(thm)], ['50', '51'])).
% 0.50/0.73  thf('53', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ (k1_relat_1 @ X1))
% 0.50/0.73          | ~ (v1_xboole_0 @ X1)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | (v1_relat_1 @ k1_xboole_0))),
% 0.50/0.73      inference('simplify', [status(thm)], ['52'])).
% 0.50/0.73  thf('54', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.50/0.73          | (v1_relat_1 @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_relat_1 @ X1)
% 0.50/0.73          | ~ (v1_xboole_0 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['23', '53'])).
% 0.50/0.73  thf('55', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | (v1_relat_1 @ k1_xboole_0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['22', '54'])).
% 0.50/0.73  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.50/0.73  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.50/0.73  thf('58', plain,
% 0.50/0.73      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.50/0.73      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.50/0.73  thf('59', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.50/0.73      inference('sup-', [status(thm)], ['21', '58'])).
% 0.50/0.73  thf('60', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0)
% 0.50/0.73          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_relat_1 @ X0))),
% 0.50/0.73      inference('demod', [status(thm)], ['20', '59'])).
% 0.50/0.73  thf('61', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.50/0.73          | ~ (v1_relat_1 @ X0))),
% 0.50/0.73      inference('simplify', [status(thm)], ['60'])).
% 0.50/0.73  thf('62', plain,
% 0.50/0.73      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.73  thf('63', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0)
% 0.50/0.73          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['61', '62'])).
% 0.50/0.73  thf('64', plain,
% 0.50/0.73      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.50/0.73  thf('65', plain,
% 0.50/0.73      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.50/0.73        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('66', plain,
% 0.50/0.73      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.50/0.73         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.50/0.73      inference('split', [status(esa)], ['65'])).
% 0.50/0.73  thf('67', plain,
% 0.50/0.73      ((![X0 : $i]:
% 0.50/0.73          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.50/0.73         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['64', '66'])).
% 0.50/0.73  thf('68', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.50/0.73      inference('demod', [status(thm)], ['45', '46'])).
% 0.50/0.73  thf('69', plain,
% 0.50/0.73      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.50/0.73  thf('70', plain,
% 0.50/0.73      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.50/0.73  thf('71', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.50/0.73      inference('sup+', [status(thm)], ['69', '70'])).
% 0.50/0.73  thf('72', plain,
% 0.50/0.73      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.50/0.73  thf('73', plain,
% 0.50/0.73      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.50/0.73         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.50/0.73      inference('split', [status(esa)], ['65'])).
% 0.50/0.73  thf('74', plain,
% 0.50/0.73      ((![X0 : $i]:
% 0.50/0.73          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.50/0.73         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['72', '73'])).
% 0.50/0.73  thf('75', plain,
% 0.50/0.73      ((![X0 : $i, X1 : $i]:
% 0.50/0.73          (((X0) != (k1_xboole_0))
% 0.50/0.73           | ~ (v1_xboole_0 @ X0)
% 0.50/0.73           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.50/0.73           | ~ (v1_xboole_0 @ X1)))
% 0.50/0.73         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['71', '74'])).
% 0.50/0.73  thf('76', plain,
% 0.50/0.73      ((![X1 : $i]:
% 0.50/0.73          (~ (v1_xboole_0 @ X1)
% 0.50/0.73           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.50/0.73           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.50/0.73         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.50/0.73      inference('simplify', [status(thm)], ['75'])).
% 0.50/0.73  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.50/0.73  thf('78', plain,
% 0.50/0.73      ((![X1 : $i]:
% 0.50/0.73          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.50/0.73         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.50/0.73      inference('simplify_reflect+', [status(thm)], ['76', '77'])).
% 0.50/0.73  thf('79', plain,
% 0.50/0.73      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.50/0.73         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['68', '78'])).
% 0.50/0.73  thf('80', plain, ((v1_relat_1 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.50/0.73  thf('82', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.50/0.73      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.50/0.73  thf('83', plain,
% 0.50/0.73      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.50/0.73       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.50/0.73      inference('split', [status(esa)], ['65'])).
% 0.50/0.73  thf('84', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.50/0.73      inference('sat_resolution*', [status(thm)], ['82', '83'])).
% 0.50/0.73  thf('85', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.73      inference('simpl_trail', [status(thm)], ['67', '84'])).
% 0.50/0.73  thf('86', plain,
% 0.50/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.50/0.73        | ~ (v1_relat_1 @ sk_A)
% 0.50/0.73        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['63', '85'])).
% 0.50/0.73  thf('87', plain, ((v1_relat_1 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.50/0.73  thf('89', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.50/0.73      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.50/0.73  thf('90', plain, ($false), inference('simplify', [status(thm)], ['89'])).
% 0.50/0.73  
% 0.50/0.73  % SZS output end Refutation
% 0.50/0.73  
% 0.58/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
