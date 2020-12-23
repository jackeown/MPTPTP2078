%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HH1KFHV0aa

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 113 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :   20
%              Number of atoms          :  584 ( 800 expanded)
%              Number of equality atoms :   54 (  85 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,
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

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

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

thf('26',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('30',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('31',plain,
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

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X10: $i] :
      ( ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('53',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('58',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['27','58'])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(simplify,[status(thm)],['62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HH1KFHV0aa
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 37 iterations in 0.013s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(cc1_relat_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.47  thf('0', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.47  thf(dt_k5_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.47       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X8)
% 0.21/0.47          | ~ (v1_relat_1 @ X9)
% 0.21/0.47          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.47  thf('2', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.47  thf(t60_relat_1, axiom,
% 0.21/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('3', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.47  thf(t47_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ B ) =>
% 0.21/0.47           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.47             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X13)
% 0.21/0.47          | ((k2_relat_1 @ (k5_relat_1 @ X13 @ X14)) = (k2_relat_1 @ X14))
% 0.21/0.47          | ~ (r1_tarski @ (k1_relat_1 @ X14) @ (k2_relat_1 @ X13))
% 0.21/0.47          | ~ (v1_relat_1 @ X14))),
% 0.21/0.47      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.47          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.47              = (k2_relat_1 @ k1_xboole_0))
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.47  thf('6', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf('7', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.47          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '8'])).
% 0.21/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.47  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf(t21_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( r1_tarski @
% 0.21/0.47         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X10 : $i]:
% 0.21/0.47         ((r1_tarski @ X10 @ 
% 0.21/0.47           (k2_zfmisc_1 @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X10)))
% 0.21/0.47          | ~ (v1_relat_1 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.21/0.47           (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.21/0.47            k1_xboole_0))
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf(t113_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '16'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '18'])).
% 0.21/0.47  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf(d10_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X0 : $i, X2 : $i]:
% 0.21/0.47         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.47  thf(t62_relat_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.47         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( v1_relat_1 @ A ) =>
% 0.21/0.47          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.47            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.21/0.47        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['26'])).
% 0.21/0.47  thf('28', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X8)
% 0.21/0.47          | ~ (v1_relat_1 @ X9)
% 0.21/0.47          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.47  thf('30', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.47  thf('31', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.47  thf(t46_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ B ) =>
% 0.21/0.47           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.47             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X11)
% 0.21/0.47          | ((k1_relat_1 @ (k5_relat_1 @ X12 @ X11)) = (k1_relat_1 @ X12))
% 0.21/0.47          | ~ (r1_tarski @ (k2_relat_1 @ X12) @ (k1_relat_1 @ X11))
% 0.21/0.47          | ~ (v1_relat_1 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.47          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.47              = (k1_relat_1 @ k1_xboole_0))
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf('35', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.47          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['30', '36'])).
% 0.21/0.47  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('39', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.47  thf('40', plain,
% 0.21/0.47      (![X10 : $i]:
% 0.21/0.47         ((r1_tarski @ X10 @ 
% 0.21/0.47           (k2_zfmisc_1 @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X10)))
% 0.21/0.47          | ~ (v1_relat_1 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.21/0.47  thf('41', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.21/0.47           (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.21/0.47            (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.47  thf('42', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.47  thf('43', plain,
% 0.21/0.47      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.47  thf('44', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['41', '43'])).
% 0.21/0.47  thf('45', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['29', '44'])).
% 0.21/0.47  thf('46', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.21/0.47          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.47  thf('47', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['28', '46'])).
% 0.21/0.47  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('49', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.47  thf('50', plain,
% 0.21/0.47      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('51', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.47  thf('52', plain,
% 0.21/0.47      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['26'])).
% 0.21/0.47  thf('53', plain,
% 0.21/0.47      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.21/0.47         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.47  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('55', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.47  thf('56', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.47  thf('57', plain,
% 0.21/0.47      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.21/0.47       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['26'])).
% 0.21/0.47  thf('58', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.21/0.47  thf('59', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['27', '58'])).
% 0.21/0.47  thf('60', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['25', '59'])).
% 0.21/0.47  thf('61', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('62', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.47  thf('63', plain, ($false), inference('simplify', [status(thm)], ['62'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
