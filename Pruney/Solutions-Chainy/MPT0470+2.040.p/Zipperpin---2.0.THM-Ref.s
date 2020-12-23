%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aQDplQamtQ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:32 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 349 expanded)
%              Number of leaves         :   28 ( 123 expanded)
%              Depth                    :   27
%              Number of atoms          : 1034 (2635 expanded)
%              Number of equality atoms :   95 ( 291 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

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
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X47 @ X46 ) ) @ ( k2_relat_1 @ X46 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('11',plain,(
    ! [X45: $i] :
      ( ( ( k3_xboole_0 @ X45 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('17',plain,(
    ! [X36: $i,X38: $i,X39: $i] :
      ( ( k2_zfmisc_1 @ X39 @ ( k4_xboole_0 @ X36 @ X38 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X39 @ X36 ) @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('20',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','21'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['12','22','23'])).

thf('25',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('28',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('29',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('34',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('35',plain,
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

thf('36',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X49 @ X48 ) )
        = ( k1_relat_1 @ X49 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X49 ) @ ( k1_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','43'])).

thf('45',plain,(
    ! [X45: $i] :
      ( ( ( k3_xboole_0 @ X45 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('49',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X36 @ X38 ) @ X37 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('52',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','53'])).

thf('55',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('59',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('62',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','64'])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','67'])).

thf('69',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X51 @ X50 ) @ X52 )
        = ( k5_relat_1 @ X51 @ ( k5_relat_1 @ X50 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X52 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('71',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('79',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','67'])).

thf('81',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('91',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['77','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['24','92'])).

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

thf('94',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('97',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['94'])).

thf('98',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['94'])).

thf('103',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['101','102'])).

thf('104',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['95','103'])).

thf('105',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(simplify,[status(thm)],['107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aQDplQamtQ
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:30:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.53/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.72  % Solved by: fo/fo7.sh
% 0.53/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.72  % done 562 iterations in 0.254s
% 0.53/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.72  % SZS output start Refutation
% 0.53/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.53/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.72  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.53/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.72  thf(cc1_relat_1, axiom,
% 0.53/0.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.53/0.72  thf('0', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 0.53/0.72      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.53/0.72  thf(t60_relat_1, axiom,
% 0.53/0.72    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.53/0.72     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.53/0.72  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.53/0.72  thf(t45_relat_1, axiom,
% 0.53/0.72    (![A:$i]:
% 0.53/0.72     ( ( v1_relat_1 @ A ) =>
% 0.53/0.72       ( ![B:$i]:
% 0.53/0.72         ( ( v1_relat_1 @ B ) =>
% 0.53/0.72           ( r1_tarski @
% 0.53/0.72             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.53/0.72  thf('2', plain,
% 0.53/0.72      (![X46 : $i, X47 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X46)
% 0.53/0.72          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X47 @ X46)) @ 
% 0.53/0.72             (k2_relat_1 @ X46))
% 0.53/0.72          | ~ (v1_relat_1 @ X47))),
% 0.53/0.72      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.53/0.72  thf('3', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.53/0.72           k1_xboole_0)
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['1', '2'])).
% 0.53/0.72  thf('4', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.53/0.72             k1_xboole_0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['0', '3'])).
% 0.53/0.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.53/0.72  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.72  thf('6', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X0)
% 0.53/0.72          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.53/0.72             k1_xboole_0))),
% 0.53/0.72      inference('demod', [status(thm)], ['4', '5'])).
% 0.53/0.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.53/0.72  thf('7', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.53/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.53/0.72  thf(d10_xboole_0, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.72  thf('8', plain,
% 0.53/0.72      (![X1 : $i, X3 : $i]:
% 0.53/0.72         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.53/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.72  thf('9', plain,
% 0.53/0.72      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.72  thf('10', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X0)
% 0.53/0.72          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['6', '9'])).
% 0.53/0.72  thf(t22_relat_1, axiom,
% 0.53/0.72    (![A:$i]:
% 0.53/0.72     ( ( v1_relat_1 @ A ) =>
% 0.53/0.72       ( ( k3_xboole_0 @
% 0.53/0.72           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.53/0.72         ( A ) ) ))).
% 0.53/0.72  thf('11', plain,
% 0.53/0.72      (![X45 : $i]:
% 0.53/0.72         (((k3_xboole_0 @ X45 @ 
% 0.53/0.72            (k2_zfmisc_1 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))) = (
% 0.53/0.72            X45))
% 0.53/0.72          | ~ (v1_relat_1 @ X45))),
% 0.53/0.72      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.53/0.72  thf('12', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((k3_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.53/0.72            (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.53/0.72             k1_xboole_0))
% 0.53/0.72            = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.72  thf(t92_xboole_1, axiom,
% 0.53/0.72    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.53/0.72  thf('13', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.72  thf(idempotence_k3_xboole_0, axiom,
% 0.53/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.53/0.72  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.53/0.72      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.53/0.72  thf(t100_xboole_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.72  thf('15', plain,
% 0.53/0.72      (![X4 : $i, X5 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ X4 @ X5)
% 0.53/0.72           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.72  thf('16', plain,
% 0.53/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['14', '15'])).
% 0.53/0.72  thf(t125_zfmisc_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.53/0.72         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.53/0.72       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.53/0.72         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.53/0.72  thf('17', plain,
% 0.53/0.72      (![X36 : $i, X38 : $i, X39 : $i]:
% 0.53/0.72         ((k2_zfmisc_1 @ X39 @ (k4_xboole_0 @ X36 @ X38))
% 0.53/0.72           = (k4_xboole_0 @ (k2_zfmisc_1 @ X39 @ X36) @ 
% 0.53/0.72              (k2_zfmisc_1 @ X39 @ X38)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.53/0.72  thf('18', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.53/0.72           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['16', '17'])).
% 0.53/0.72  thf('19', plain,
% 0.53/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['14', '15'])).
% 0.53/0.72  thf('20', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.72  thf('21', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.53/0.72      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.53/0.72  thf('22', plain,
% 0.53/0.72      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['13', '21'])).
% 0.53/0.72  thf(t2_boole, axiom,
% 0.53/0.72    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.53/0.72  thf('23', plain,
% 0.53/0.72      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.53/0.72  thf('24', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['12', '22', '23'])).
% 0.53/0.72  thf('25', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.72  thf('26', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 0.53/0.72      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.53/0.72  thf(dt_k5_relat_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.53/0.72       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.53/0.72  thf('27', plain,
% 0.53/0.72      (![X43 : $i, X44 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X43)
% 0.53/0.72          | ~ (v1_relat_1 @ X44)
% 0.53/0.72          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.53/0.72      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.53/0.72  thf('28', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.72  thf('29', plain,
% 0.53/0.72      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.53/0.72  thf('30', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['28', '29'])).
% 0.53/0.72  thf('31', plain,
% 0.53/0.72      (![X4 : $i, X5 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ X4 @ X5)
% 0.53/0.72           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.72  thf('32', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.53/0.72           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['30', '31'])).
% 0.53/0.72  thf('33', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.72  thf('34', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 0.53/0.72      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.53/0.72  thf('35', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.53/0.72  thf(t46_relat_1, axiom,
% 0.53/0.72    (![A:$i]:
% 0.53/0.72     ( ( v1_relat_1 @ A ) =>
% 0.53/0.72       ( ![B:$i]:
% 0.53/0.72         ( ( v1_relat_1 @ B ) =>
% 0.53/0.72           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.53/0.72             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.53/0.72  thf('36', plain,
% 0.53/0.72      (![X48 : $i, X49 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X48)
% 0.53/0.72          | ((k1_relat_1 @ (k5_relat_1 @ X49 @ X48)) = (k1_relat_1 @ X49))
% 0.53/0.72          | ~ (r1_tarski @ (k2_relat_1 @ X49) @ (k1_relat_1 @ X48))
% 0.53/0.72          | ~ (v1_relat_1 @ X49))),
% 0.53/0.72      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.53/0.72  thf('37', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.53/0.72          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.53/0.72          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.53/0.72              = (k1_relat_1 @ k1_xboole_0))
% 0.53/0.72          | ~ (v1_relat_1 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['35', '36'])).
% 0.53/0.72  thf('38', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.53/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.53/0.72  thf('39', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.53/0.72  thf('40', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ k1_xboole_0)
% 0.53/0.72          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.53/0.72          | ~ (v1_relat_1 @ X0))),
% 0.53/0.72      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.53/0.72  thf('41', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['34', '40'])).
% 0.53/0.72  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.72  thf('43', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X0)
% 0.53/0.72          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['41', '42'])).
% 0.53/0.72  thf('44', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (((k1_relat_1 @ (k5_relat_1 @ (k5_xboole_0 @ X0 @ X0) @ X1))
% 0.53/0.72            = (k1_xboole_0))
% 0.53/0.72          | ~ (v1_relat_1 @ X1))),
% 0.53/0.72      inference('sup+', [status(thm)], ['33', '43'])).
% 0.53/0.72  thf('45', plain,
% 0.53/0.72      (![X45 : $i]:
% 0.53/0.72         (((k3_xboole_0 @ X45 @ 
% 0.53/0.72            (k2_zfmisc_1 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))) = (
% 0.53/0.72            X45))
% 0.53/0.72          | ~ (v1_relat_1 @ X45))),
% 0.53/0.72      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.53/0.72  thf('46', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (((k3_xboole_0 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) @ 
% 0.53/0.72            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.53/0.72             (k2_relat_1 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0))))
% 0.53/0.72            = (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0))
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['44', '45'])).
% 0.53/0.72  thf('47', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.72  thf('48', plain,
% 0.53/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['14', '15'])).
% 0.53/0.72  thf('49', plain,
% 0.53/0.72      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.53/0.72         ((k2_zfmisc_1 @ (k4_xboole_0 @ X36 @ X38) @ X37)
% 0.53/0.72           = (k4_xboole_0 @ (k2_zfmisc_1 @ X36 @ X37) @ 
% 0.53/0.72              (k2_zfmisc_1 @ X38 @ X37)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.53/0.72  thf('50', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.53/0.72           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['48', '49'])).
% 0.53/0.72  thf('51', plain,
% 0.53/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['14', '15'])).
% 0.53/0.72  thf('52', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.72  thf('53', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 0.53/0.72      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.53/0.72  thf('54', plain,
% 0.53/0.72      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['47', '53'])).
% 0.53/0.72  thf('55', plain,
% 0.53/0.72      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.53/0.72  thf('56', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (((k1_xboole_0) = (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0))
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['46', '54', '55'])).
% 0.53/0.72  thf('57', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ 
% 0.53/0.72             (k5_relat_1 @ 
% 0.53/0.72              (k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)) @ X1))
% 0.53/0.72          | ~ (v1_relat_1 @ X1)
% 0.53/0.72          | ((k1_xboole_0)
% 0.53/0.72              = (k5_relat_1 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X1)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['32', '56'])).
% 0.53/0.72  thf('58', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.53/0.72           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['30', '31'])).
% 0.53/0.72  thf('59', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.72  thf('60', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['58', '59'])).
% 0.53/0.72  thf('61', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.72  thf('62', plain,
% 0.53/0.72      (![X1 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X1))
% 0.53/0.72          | ~ (v1_relat_1 @ X1)
% 0.53/0.72          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X1)))),
% 0.53/0.72      inference('demod', [status(thm)], ['57', '60', '61'])).
% 0.53/0.72  thf('63', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X0)
% 0.53/0.72          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.53/0.72          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.53/0.72          | ~ (v1_relat_1 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['27', '62'])).
% 0.53/0.72  thf('64', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.53/0.72          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.53/0.72          | ~ (v1_relat_1 @ X0))),
% 0.53/0.72      inference('simplify', [status(thm)], ['63'])).
% 0.53/0.72  thf('65', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['26', '64'])).
% 0.53/0.72  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.72  thf('67', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X0)
% 0.53/0.72          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['65', '66'])).
% 0.53/0.72  thf('68', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (((k1_xboole_0) = (k5_relat_1 @ (k5_xboole_0 @ X0 @ X0) @ X1))
% 0.53/0.72          | ~ (v1_relat_1 @ X1))),
% 0.53/0.72      inference('sup+', [status(thm)], ['25', '67'])).
% 0.53/0.72  thf('69', plain,
% 0.53/0.72      (![X43 : $i, X44 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X43)
% 0.53/0.72          | ~ (v1_relat_1 @ X44)
% 0.53/0.72          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.53/0.72      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.53/0.72  thf(t55_relat_1, axiom,
% 0.53/0.72    (![A:$i]:
% 0.53/0.72     ( ( v1_relat_1 @ A ) =>
% 0.53/0.72       ( ![B:$i]:
% 0.53/0.72         ( ( v1_relat_1 @ B ) =>
% 0.53/0.72           ( ![C:$i]:
% 0.53/0.72             ( ( v1_relat_1 @ C ) =>
% 0.53/0.72               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.53/0.72                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.53/0.72  thf('70', plain,
% 0.53/0.72      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X50)
% 0.53/0.72          | ((k5_relat_1 @ (k5_relat_1 @ X51 @ X50) @ X52)
% 0.53/0.72              = (k5_relat_1 @ X51 @ (k5_relat_1 @ X50 @ X52)))
% 0.53/0.72          | ~ (v1_relat_1 @ X52)
% 0.53/0.72          | ~ (v1_relat_1 @ X51))),
% 0.53/0.72      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.53/0.72  thf('71', plain,
% 0.53/0.72      (![X43 : $i, X44 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X43)
% 0.53/0.72          | ~ (v1_relat_1 @ X44)
% 0.53/0.72          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.53/0.72      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.53/0.72  thf('72', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 0.53/0.72          | ~ (v1_relat_1 @ X2)
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | ~ (v1_relat_1 @ X1)
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['70', '71'])).
% 0.53/0.72  thf('73', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 0.53/0.72          | ~ (v1_relat_1 @ X1)
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | ~ (v1_relat_1 @ X2)
% 0.53/0.72          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 0.53/0.72      inference('simplify', [status(thm)], ['72'])).
% 0.53/0.72  thf('74', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X0)
% 0.53/0.72          | ~ (v1_relat_1 @ X1)
% 0.53/0.72          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 0.53/0.72          | ~ (v1_relat_1 @ X1)
% 0.53/0.72          | ~ (v1_relat_1 @ X2)
% 0.53/0.72          | ~ (v1_relat_1 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['69', '73'])).
% 0.53/0.72  thf('75', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X2)
% 0.53/0.72          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 0.53/0.72          | ~ (v1_relat_1 @ X1)
% 0.53/0.72          | ~ (v1_relat_1 @ X0))),
% 0.53/0.72      inference('simplify', [status(thm)], ['74'])).
% 0.53/0.72  thf('76', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         ((v1_relat_1 @ (k5_relat_1 @ X2 @ k1_xboole_0))
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | ~ (v1_relat_1 @ (k5_xboole_0 @ X1 @ X1))
% 0.53/0.72          | ~ (v1_relat_1 @ X2)
% 0.53/0.72          | ~ (v1_relat_1 @ X0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['68', '75'])).
% 0.53/0.72  thf('77', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X2)
% 0.53/0.72          | ~ (v1_relat_1 @ (k5_xboole_0 @ X1 @ X1))
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | (v1_relat_1 @ (k5_relat_1 @ X2 @ k1_xboole_0)))),
% 0.53/0.72      inference('simplify', [status(thm)], ['76'])).
% 0.53/0.72  thf('78', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.72  thf('79', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 0.53/0.72      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.53/0.72  thf('80', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (((k1_xboole_0) = (k5_relat_1 @ (k5_xboole_0 @ X0 @ X0) @ X1))
% 0.53/0.72          | ~ (v1_relat_1 @ X1))),
% 0.53/0.72      inference('sup+', [status(thm)], ['25', '67'])).
% 0.53/0.72  thf('81', plain,
% 0.53/0.72      (![X43 : $i, X44 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X43)
% 0.53/0.72          | ~ (v1_relat_1 @ X44)
% 0.53/0.72          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.53/0.72      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.53/0.72  thf('82', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((v1_relat_1 @ k1_xboole_0)
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | ~ (v1_relat_1 @ (k5_xboole_0 @ X1 @ X1)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['80', '81'])).
% 0.53/0.72  thf('83', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ (k5_xboole_0 @ X1 @ X1))
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | (v1_relat_1 @ k1_xboole_0))),
% 0.53/0.72      inference('simplify', [status(thm)], ['82'])).
% 0.53/0.72  thf('84', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0)) | (v1_relat_1 @ k1_xboole_0))),
% 0.53/0.72      inference('condensation', [status(thm)], ['83'])).
% 0.53/0.72  thf('85', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))
% 0.53/0.72          | (v1_relat_1 @ k1_xboole_0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['79', '84'])).
% 0.53/0.72  thf('86', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.72  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.72  thf('88', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['86', '87'])).
% 0.53/0.72  thf('89', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.53/0.72      inference('demod', [status(thm)], ['85', '88'])).
% 0.53/0.72  thf('90', plain, (![X0 : $i]: (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['78', '89'])).
% 0.53/0.72  thf('91', plain,
% 0.53/0.72      (![X0 : $i, X2 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X2)
% 0.53/0.72          | ~ (v1_relat_1 @ X0)
% 0.53/0.72          | (v1_relat_1 @ (k5_relat_1 @ X2 @ k1_xboole_0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['77', '90'])).
% 0.53/0.72  thf('92', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.53/0.72      inference('condensation', [status(thm)], ['91'])).
% 0.53/0.72  thf('93', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X0)
% 0.53/0.72          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.53/0.72      inference('clc', [status(thm)], ['24', '92'])).
% 0.53/0.72  thf(t62_relat_1, conjecture,
% 0.53/0.72    (![A:$i]:
% 0.53/0.72     ( ( v1_relat_1 @ A ) =>
% 0.53/0.72       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.53/0.72         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.53/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.72    (~( ![A:$i]:
% 0.53/0.72        ( ( v1_relat_1 @ A ) =>
% 0.53/0.72          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.53/0.72            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.53/0.72    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.53/0.72  thf('94', plain,
% 0.53/0.72      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.53/0.72        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('95', plain,
% 0.53/0.72      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.53/0.72         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.53/0.72      inference('split', [status(esa)], ['94'])).
% 0.53/0.72  thf('96', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X0)
% 0.53/0.72          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['65', '66'])).
% 0.53/0.72  thf('97', plain,
% 0.53/0.72      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.53/0.72         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.53/0.72      inference('split', [status(esa)], ['94'])).
% 0.53/0.72  thf('98', plain,
% 0.53/0.72      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.53/0.72         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.53/0.72      inference('sup-', [status(thm)], ['96', '97'])).
% 0.53/0.72  thf('99', plain, ((v1_relat_1 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('100', plain,
% 0.53/0.72      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.53/0.72         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.53/0.72      inference('demod', [status(thm)], ['98', '99'])).
% 0.53/0.72  thf('101', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('simplify', [status(thm)], ['100'])).
% 0.53/0.72  thf('102', plain,
% 0.53/0.72      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.53/0.72       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('split', [status(esa)], ['94'])).
% 0.53/0.72  thf('103', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.53/0.72      inference('sat_resolution*', [status(thm)], ['101', '102'])).
% 0.53/0.72  thf('104', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.53/0.72      inference('simpl_trail', [status(thm)], ['95', '103'])).
% 0.53/0.72  thf('105', plain,
% 0.53/0.72      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.53/0.72      inference('sup-', [status(thm)], ['93', '104'])).
% 0.53/0.72  thf('106', plain, ((v1_relat_1 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('107', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.53/0.72      inference('demod', [status(thm)], ['105', '106'])).
% 0.53/0.72  thf('108', plain, ($false), inference('simplify', [status(thm)], ['107'])).
% 0.53/0.72  
% 0.53/0.72  % SZS output end Refutation
% 0.53/0.72  
% 0.53/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
