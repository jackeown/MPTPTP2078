%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wKC3gDPUij

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 137 expanded)
%              Number of leaves         :   21 (  48 expanded)
%              Depth                    :   19
%              Number of atoms          :  641 ( 906 expanded)
%              Number of equality atoms :   69 ( 103 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) ) @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X12: $i] :
      ( ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
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

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('16',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
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

thf('30',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('35',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('36',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X12: $i] :
      ( ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('47',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('61',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('69',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['32','69'])).

thf('71',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('74',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    $false ),
    inference(simplify,[status(thm)],['74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wKC3gDPUij
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:10:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.61  % Solved by: fo/fo7.sh
% 0.21/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.61  % done 358 iterations in 0.151s
% 0.21/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.61  % SZS output start Refutation
% 0.21/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.61  thf(cc1_relat_1, axiom,
% 0.21/0.61    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.61  thf('0', plain, (![X8 : $i]: ((v1_relat_1 @ X8) | ~ (v1_xboole_0 @ X8))),
% 0.21/0.61      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.61  thf(dt_k5_relat_1, axiom,
% 0.21/0.61    (![A:$i,B:$i]:
% 0.21/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.61       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.61  thf('1', plain,
% 0.21/0.61      (![X9 : $i, X10 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X9)
% 0.21/0.61          | ~ (v1_relat_1 @ X10)
% 0.21/0.61          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.21/0.61      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.61  thf('2', plain, (![X8 : $i]: ((v1_relat_1 @ X8) | ~ (v1_xboole_0 @ X8))),
% 0.21/0.61      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.61  thf(t60_relat_1, axiom,
% 0.21/0.61    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.61     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.61  thf('3', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.61  thf(t45_relat_1, axiom,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( v1_relat_1 @ A ) =>
% 0.21/0.61       ( ![B:$i]:
% 0.21/0.61         ( ( v1_relat_1 @ B ) =>
% 0.21/0.61           ( r1_tarski @
% 0.21/0.61             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.21/0.61  thf('4', plain,
% 0.21/0.61      (![X15 : $i, X16 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X15)
% 0.21/0.61          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X16 @ X15)) @ 
% 0.21/0.61             (k2_relat_1 @ X15))
% 0.21/0.61          | ~ (v1_relat_1 @ X16))),
% 0.21/0.61      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.21/0.61  thf('5', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.21/0.61           k1_xboole_0)
% 0.21/0.61          | ~ (v1_relat_1 @ X0)
% 0.21/0.61          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.61  thf('6', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.61          | ~ (v1_relat_1 @ X0)
% 0.21/0.61          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.21/0.61             k1_xboole_0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.61  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.61  thf('8', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.21/0.61             k1_xboole_0))),
% 0.21/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.61  thf('9', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.61  thf(d10_xboole_0, axiom,
% 0.21/0.61    (![A:$i,B:$i]:
% 0.21/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.61  thf('10', plain,
% 0.21/0.61      (![X1 : $i, X3 : $i]:
% 0.21/0.61         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.21/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.61  thf('11', plain,
% 0.21/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.61  thf('12', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.61  thf(t21_relat_1, axiom,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( v1_relat_1 @ A ) =>
% 0.21/0.61       ( r1_tarski @
% 0.21/0.61         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.61  thf('13', plain,
% 0.21/0.61      (![X12 : $i]:
% 0.21/0.61         ((r1_tarski @ X12 @ 
% 0.21/0.61           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.21/0.61          | ~ (v1_relat_1 @ X12))),
% 0.21/0.61      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.21/0.61  thf(l13_xboole_0, axiom,
% 0.21/0.61    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.61  thf('14', plain,
% 0.21/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.61  thf(t113_zfmisc_1, axiom,
% 0.21/0.61    (![A:$i,B:$i]:
% 0.21/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.61  thf('15', plain,
% 0.21/0.61      (![X6 : $i, X7 : $i]:
% 0.21/0.61         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.21/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.61  thf('16', plain,
% 0.21/0.61      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.61  thf('17', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.61      inference('sup+', [status(thm)], ['14', '16'])).
% 0.21/0.61  thf('18', plain,
% 0.21/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.61  thf('19', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.61         (~ (r1_tarski @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.61          | ~ (v1_xboole_0 @ X0)
% 0.21/0.61          | ((X2) = (k1_xboole_0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.61  thf('20', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((X0) = (k1_xboole_0))
% 0.21/0.61          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['13', '19'])).
% 0.21/0.61  thf('21', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.61          | ~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.61          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['12', '20'])).
% 0.21/0.61  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.61  thf('23', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.61          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.61      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.61  thf('24', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.61          | ~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.61          | ~ (v1_relat_1 @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['1', '23'])).
% 0.21/0.61  thf('25', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.61          | ~ (v1_relat_1 @ X0)
% 0.21/0.61          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.61  thf('26', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.61          | ~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['0', '25'])).
% 0.21/0.61  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.61  thf('28', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.61  thf('29', plain,
% 0.21/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.61  thf(t62_relat_1, conjecture,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( v1_relat_1 @ A ) =>
% 0.21/0.61       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.61         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.61    (~( ![A:$i]:
% 0.21/0.61        ( ( v1_relat_1 @ A ) =>
% 0.21/0.61          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.61            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.61    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.21/0.61  thf('30', plain,
% 0.21/0.61      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.21/0.61        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('31', plain,
% 0.21/0.61      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.61         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.61      inference('split', [status(esa)], ['30'])).
% 0.21/0.61  thf('32', plain,
% 0.21/0.61      ((![X0 : $i]:
% 0.21/0.61          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.21/0.61         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.61      inference('sup-', [status(thm)], ['29', '31'])).
% 0.21/0.61  thf('33', plain, (![X8 : $i]: ((v1_relat_1 @ X8) | ~ (v1_xboole_0 @ X8))),
% 0.21/0.61      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.61  thf('34', plain,
% 0.21/0.61      (![X9 : $i, X10 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X9)
% 0.21/0.61          | ~ (v1_relat_1 @ X10)
% 0.21/0.61          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.21/0.61      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.61  thf('35', plain, (![X8 : $i]: ((v1_relat_1 @ X8) | ~ (v1_xboole_0 @ X8))),
% 0.21/0.61      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.61  thf('36', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.61  thf(t44_relat_1, axiom,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( v1_relat_1 @ A ) =>
% 0.21/0.61       ( ![B:$i]:
% 0.21/0.61         ( ( v1_relat_1 @ B ) =>
% 0.21/0.61           ( r1_tarski @
% 0.21/0.61             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.21/0.61  thf('37', plain,
% 0.21/0.61      (![X13 : $i, X14 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X13)
% 0.21/0.61          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X14 @ X13)) @ 
% 0.21/0.61             (k1_relat_1 @ X14))
% 0.21/0.61          | ~ (v1_relat_1 @ X14))),
% 0.21/0.61      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.21/0.61  thf('38', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.21/0.61           k1_xboole_0)
% 0.21/0.61          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.61          | ~ (v1_relat_1 @ X0))),
% 0.21/0.61      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.61  thf('39', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.61          | ~ (v1_relat_1 @ X0)
% 0.21/0.61          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.21/0.61             k1_xboole_0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['35', '38'])).
% 0.21/0.61  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.61  thf('41', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.21/0.61             k1_xboole_0))),
% 0.21/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.61  thf('42', plain,
% 0.21/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.61  thf('43', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.61  thf('44', plain,
% 0.21/0.61      (![X12 : $i]:
% 0.21/0.61         ((r1_tarski @ X12 @ 
% 0.21/0.61           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.21/0.61          | ~ (v1_relat_1 @ X12))),
% 0.21/0.61      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.21/0.61  thf('45', plain,
% 0.21/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.61  thf('46', plain,
% 0.21/0.61      (![X6 : $i, X7 : $i]:
% 0.21/0.61         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.21/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.61  thf('47', plain,
% 0.21/0.61      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.21/0.61      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.61  thf('48', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.61      inference('sup+', [status(thm)], ['45', '47'])).
% 0.21/0.61  thf('49', plain,
% 0.21/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.61  thf('50', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.61         (~ (r1_tarski @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.61          | ~ (v1_xboole_0 @ X1)
% 0.21/0.61          | ((X2) = (k1_xboole_0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.61  thf('51', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((X0) = (k1_xboole_0))
% 0.21/0.61          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['44', '50'])).
% 0.21/0.61  thf('52', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.61          | ~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.21/0.61          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['43', '51'])).
% 0.21/0.61  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.61  thf('54', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.21/0.61          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.61      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.61  thf('55', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.61          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.21/0.61          | ~ (v1_relat_1 @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['34', '54'])).
% 0.21/0.61  thf('56', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.21/0.61          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.61          | ~ (v1_relat_1 @ X0))),
% 0.21/0.61      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.61  thf('57', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.61          | ~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['33', '56'])).
% 0.21/0.61  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.61  thf('59', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.61      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.61  thf('60', plain,
% 0.21/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.61  thf('61', plain,
% 0.21/0.61      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.21/0.61         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.61      inference('split', [status(esa)], ['30'])).
% 0.21/0.61  thf('62', plain,
% 0.21/0.61      ((![X0 : $i]:
% 0.21/0.61          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.21/0.61         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.61      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.61  thf('63', plain,
% 0.21/0.61      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.61         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.61         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.21/0.61         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.61      inference('sup-', [status(thm)], ['59', '62'])).
% 0.21/0.61  thf('64', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.61  thf('66', plain,
% 0.21/0.61      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.61         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.61      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.21/0.61  thf('67', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.61      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.61  thf('68', plain,
% 0.21/0.61      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.21/0.61       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.61      inference('split', [status(esa)], ['30'])).
% 0.21/0.61  thf('69', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.61      inference('sat_resolution*', [status(thm)], ['67', '68'])).
% 0.21/0.61  thf('70', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.61      inference('simpl_trail', [status(thm)], ['32', '69'])).
% 0.21/0.61  thf('71', plain,
% 0.21/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.61        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.61        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['28', '70'])).
% 0.21/0.61  thf('72', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.61  thf('74', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.61      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.21/0.61  thf('75', plain, ($false), inference('simplify', [status(thm)], ['74'])).
% 0.21/0.61  
% 0.21/0.61  % SZS output end Refutation
% 0.21/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
