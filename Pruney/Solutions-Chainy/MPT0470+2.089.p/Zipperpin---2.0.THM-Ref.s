%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6NxabVLa98

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:39 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 305 expanded)
%              Number of leaves         :   26 ( 109 expanded)
%              Depth                    :   25
%              Number of atoms          : 1064 (2264 expanded)
%              Number of equality atoms :  118 ( 278 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ~ ( v1_relat_1 @ X41 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X39: $i] :
      ( ( v1_relat_1 @ X39 )
      | ~ ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,
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

thf('9',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X45 @ X46 ) )
        = ( k2_relat_1 @ X46 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X46 ) @ ( k2_relat_1 @ X45 ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
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
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
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
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','16'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('18',plain,(
    ! [X42: $i] :
      ( ( ( k3_xboole_0 @ X42 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X42 ) @ ( k2_relat_1 @ X42 ) ) )
        = X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('24',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ X36 @ ( k4_xboole_0 @ X33 @ X35 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X36 @ X33 ) @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('27',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('34',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('37',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['32','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','37'])).

thf('39',plain,(
    ! [X39: $i] :
      ( ( v1_relat_1 @ X39 )
      | ~ ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('41',plain,(
    ! [X39: $i] :
      ( ( v1_relat_1 @ X39 )
      | ~ ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('42',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ~ ( v1_relat_1 @ X41 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('45',plain,(
    ! [X39: $i] :
      ( ( v1_relat_1 @ X39 )
      | ~ ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('46',plain,
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

thf('47',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X44 @ X43 ) )
        = ( k1_relat_1 @ X44 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X44 ) @ ( k1_relat_1 @ X43 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','54'])).

thf('56',plain,(
    ! [X42: $i] :
      ( ( ( k3_xboole_0 @ X42 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X42 ) @ ( k2_relat_1 @ X42 ) ) )
        = X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('60',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X33 @ X35 ) @ X34 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('63',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','64'])).

thf('66',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('70',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('71',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','73'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','76'])).

thf('78',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ~ ( v1_relat_1 @ X41 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','81'])).

thf('83',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('90',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('92',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

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

thf('93',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['93'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ( k5_relat_1 @ sk_A @ ( k5_xboole_0 @ X0 @ X0 ) )
       != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( k5_relat_1 @ sk_A @ ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
       != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','95'])).

thf('97',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k5_relat_1 @ sk_A @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X1 @ X1 ) ) )
       != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( k5_relat_1 @ sk_A @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) )
       != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','97'])).

thf('99',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('100',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('102',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['93'])).

thf('103',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['93'])).

thf('108',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['106','107'])).

thf('109',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['100','108'])).

thf('110',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    $false ),
    inference(simplify,[status(thm)],['112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6NxabVLa98
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.52  % Solved by: fo/fo7.sh
% 0.35/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.52  % done 208 iterations in 0.068s
% 0.35/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.52  % SZS output start Refutation
% 0.35/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.35/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.52  thf(dt_k5_relat_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.35/0.52       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.35/0.52  thf('0', plain,
% 0.35/0.52      (![X40 : $i, X41 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X40)
% 0.35/0.52          | ~ (v1_relat_1 @ X41)
% 0.35/0.52          | (v1_relat_1 @ (k5_relat_1 @ X40 @ X41)))),
% 0.35/0.52      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.35/0.52  thf(t92_xboole_1, axiom,
% 0.35/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.52  thf('1', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf(t2_boole, axiom,
% 0.35/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.35/0.52  thf('2', plain,
% 0.35/0.52      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.35/0.52  thf(t100_xboole_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.52  thf('3', plain,
% 0.35/0.52      (![X1 : $i, X2 : $i]:
% 0.35/0.52         ((k4_xboole_0 @ X1 @ X2)
% 0.35/0.52           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.52  thf('4', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.35/0.52  thf('5', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.35/0.52           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['1', '4'])).
% 0.35/0.52  thf('6', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf(cc1_relat_1, axiom,
% 0.35/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.35/0.52  thf('7', plain, (![X39 : $i]: ((v1_relat_1 @ X39) | ~ (v1_xboole_0 @ X39))),
% 0.35/0.52      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.35/0.52  thf(t60_relat_1, axiom,
% 0.35/0.52    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.35/0.52     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.35/0.52  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.52  thf(t47_relat_1, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ A ) =>
% 0.35/0.52       ( ![B:$i]:
% 0.35/0.52         ( ( v1_relat_1 @ B ) =>
% 0.35/0.52           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.35/0.52             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.35/0.52  thf('9', plain,
% 0.35/0.52      (![X45 : $i, X46 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X45)
% 0.35/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X45 @ X46)) = (k2_relat_1 @ X46))
% 0.35/0.52          | ~ (r1_tarski @ (k1_relat_1 @ X46) @ (k2_relat_1 @ X45))
% 0.35/0.52          | ~ (v1_relat_1 @ X46))),
% 0.35/0.52      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.35/0.52  thf('10', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.35/0.52          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.35/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.35/0.52              = (k2_relat_1 @ k1_xboole_0))
% 0.35/0.52          | ~ (v1_relat_1 @ X0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.35/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.52  thf('11', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.35/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.52  thf('12', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.52  thf('13', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ k1_xboole_0)
% 0.35/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.35/0.52          | ~ (v1_relat_1 @ X0))),
% 0.35/0.52      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.35/0.52  thf('14', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.35/0.52          | ~ (v1_relat_1 @ X0)
% 0.35/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['7', '13'])).
% 0.35/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.35/0.52  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.35/0.52  thf('16', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X0)
% 0.35/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.35/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.35/0.52  thf('17', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (((k2_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 0.35/0.52            = (k1_xboole_0))
% 0.35/0.52          | ~ (v1_relat_1 @ X1))),
% 0.35/0.52      inference('sup+', [status(thm)], ['6', '16'])).
% 0.35/0.52  thf(t22_relat_1, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ A ) =>
% 0.35/0.52       ( ( k3_xboole_0 @
% 0.35/0.52           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.35/0.52         ( A ) ) ))).
% 0.35/0.52  thf('18', plain,
% 0.35/0.52      (![X42 : $i]:
% 0.35/0.52         (((k3_xboole_0 @ X42 @ 
% 0.35/0.52            (k2_zfmisc_1 @ (k1_relat_1 @ X42) @ (k2_relat_1 @ X42))) = (
% 0.35/0.52            X42))
% 0.35/0.52          | ~ (v1_relat_1 @ X42))),
% 0.35/0.52      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.35/0.52  thf('19', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (((k3_xboole_0 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ 
% 0.35/0.52            (k2_zfmisc_1 @ 
% 0.35/0.52             (k1_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0))) @ 
% 0.35/0.52             k1_xboole_0))
% 0.35/0.52            = (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 0.35/0.52          | ~ (v1_relat_1 @ X1)
% 0.35/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0))))),
% 0.35/0.52      inference('sup+', [status(thm)], ['17', '18'])).
% 0.35/0.52  thf('20', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf(idempotence_k3_xboole_0, axiom,
% 0.35/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.35/0.52  thf('21', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.35/0.52      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.35/0.52  thf('22', plain,
% 0.35/0.52      (![X1 : $i, X2 : $i]:
% 0.35/0.52         ((k4_xboole_0 @ X1 @ X2)
% 0.35/0.52           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.52  thf('23', plain,
% 0.35/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.35/0.52  thf(t125_zfmisc_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.35/0.52         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.35/0.52       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.35/0.52         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.35/0.52  thf('24', plain,
% 0.35/0.52      (![X33 : $i, X35 : $i, X36 : $i]:
% 0.35/0.52         ((k2_zfmisc_1 @ X36 @ (k4_xboole_0 @ X33 @ X35))
% 0.35/0.52           = (k4_xboole_0 @ (k2_zfmisc_1 @ X36 @ X33) @ 
% 0.35/0.52              (k2_zfmisc_1 @ X36 @ X35)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.35/0.52  thf('25', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.35/0.52           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.35/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.35/0.52  thf('26', plain,
% 0.35/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.35/0.52  thf('27', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf('28', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         ((k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.35/0.52      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.35/0.52  thf('29', plain,
% 0.35/0.52      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['20', '28'])).
% 0.35/0.52  thf('30', plain,
% 0.35/0.52      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.35/0.52  thf('31', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (((k1_xboole_0) = (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 0.35/0.52          | ~ (v1_relat_1 @ X1)
% 0.35/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0))))),
% 0.35/0.52      inference('demod', [status(thm)], ['19', '29', '30'])).
% 0.35/0.52  thf('32', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ 
% 0.35/0.52             (k5_relat_1 @ X1 @ 
% 0.35/0.52              (k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))))
% 0.35/0.52          | ~ (v1_relat_1 @ X1)
% 0.35/0.52          | ((k1_xboole_0)
% 0.35/0.52              = (k5_relat_1 @ X1 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['5', '31'])).
% 0.35/0.52  thf('33', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.35/0.52           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['1', '4'])).
% 0.35/0.52  thf('34', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf('35', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['33', '34'])).
% 0.35/0.52  thf('36', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf('37', plain,
% 0.35/0.52      (![X1 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ k1_xboole_0))
% 0.35/0.52          | ~ (v1_relat_1 @ X1)
% 0.35/0.52          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ k1_xboole_0)))),
% 0.35/0.52      inference('demod', [status(thm)], ['32', '35', '36'])).
% 0.35/0.52  thf('38', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ k1_xboole_0)
% 0.35/0.52          | ~ (v1_relat_1 @ X0)
% 0.35/0.52          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.35/0.52          | ~ (v1_relat_1 @ X0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['0', '37'])).
% 0.35/0.52  thf('39', plain, (![X39 : $i]: ((v1_relat_1 @ X39) | ~ (v1_xboole_0 @ X39))),
% 0.35/0.52      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.35/0.52  thf('40', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf('41', plain, (![X39 : $i]: ((v1_relat_1 @ X39) | ~ (v1_xboole_0 @ X39))),
% 0.35/0.52      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.35/0.52  thf('42', plain,
% 0.35/0.52      (![X40 : $i, X41 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X40)
% 0.35/0.52          | ~ (v1_relat_1 @ X41)
% 0.35/0.52          | (v1_relat_1 @ (k5_relat_1 @ X40 @ X41)))),
% 0.35/0.52      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.35/0.52  thf('43', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.35/0.52           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['1', '4'])).
% 0.35/0.52  thf('44', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf('45', plain, (![X39 : $i]: ((v1_relat_1 @ X39) | ~ (v1_xboole_0 @ X39))),
% 0.35/0.52      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.35/0.52  thf('46', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.52  thf(t46_relat_1, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ A ) =>
% 0.35/0.52       ( ![B:$i]:
% 0.35/0.52         ( ( v1_relat_1 @ B ) =>
% 0.35/0.52           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.52             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.35/0.52  thf('47', plain,
% 0.35/0.52      (![X43 : $i, X44 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X43)
% 0.35/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X44 @ X43)) = (k1_relat_1 @ X44))
% 0.35/0.52          | ~ (r1_tarski @ (k2_relat_1 @ X44) @ (k1_relat_1 @ X43))
% 0.35/0.52          | ~ (v1_relat_1 @ X44))),
% 0.35/0.52      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.35/0.52  thf('48', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.35/0.52          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.35/0.52          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.35/0.52              = (k1_relat_1 @ k1_xboole_0))
% 0.35/0.52          | ~ (v1_relat_1 @ X0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.35/0.52  thf('49', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.35/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.52  thf('50', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.52  thf('51', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ k1_xboole_0)
% 0.35/0.52          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.35/0.52          | ~ (v1_relat_1 @ X0))),
% 0.35/0.52      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.35/0.52  thf('52', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.35/0.52          | ~ (v1_relat_1 @ X0)
% 0.35/0.52          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['45', '51'])).
% 0.35/0.52  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.35/0.52  thf('54', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X0)
% 0.35/0.52          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.35/0.52      inference('demod', [status(thm)], ['52', '53'])).
% 0.35/0.52  thf('55', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (((k1_relat_1 @ (k5_relat_1 @ (k5_xboole_0 @ X0 @ X0) @ X1))
% 0.35/0.52            = (k1_xboole_0))
% 0.35/0.52          | ~ (v1_relat_1 @ X1))),
% 0.35/0.52      inference('sup+', [status(thm)], ['44', '54'])).
% 0.35/0.52  thf('56', plain,
% 0.35/0.52      (![X42 : $i]:
% 0.35/0.52         (((k3_xboole_0 @ X42 @ 
% 0.35/0.52            (k2_zfmisc_1 @ (k1_relat_1 @ X42) @ (k2_relat_1 @ X42))) = (
% 0.35/0.52            X42))
% 0.35/0.52          | ~ (v1_relat_1 @ X42))),
% 0.35/0.52      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.35/0.52  thf('57', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (((k3_xboole_0 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) @ 
% 0.35/0.52            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.35/0.52             (k2_relat_1 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0))))
% 0.35/0.52            = (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0))
% 0.35/0.52          | ~ (v1_relat_1 @ X0)
% 0.35/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0)))),
% 0.35/0.52      inference('sup+', [status(thm)], ['55', '56'])).
% 0.35/0.52  thf('58', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf('59', plain,
% 0.35/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.35/0.52  thf('60', plain,
% 0.35/0.52      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.52         ((k2_zfmisc_1 @ (k4_xboole_0 @ X33 @ X35) @ X34)
% 0.35/0.52           = (k4_xboole_0 @ (k2_zfmisc_1 @ X33 @ X34) @ 
% 0.35/0.52              (k2_zfmisc_1 @ X35 @ X34)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.35/0.52  thf('61', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.35/0.52           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.35/0.52      inference('sup+', [status(thm)], ['59', '60'])).
% 0.35/0.52  thf('62', plain,
% 0.35/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.35/0.52  thf('63', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf('64', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 0.35/0.52      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.35/0.52  thf('65', plain,
% 0.35/0.52      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['58', '64'])).
% 0.35/0.52  thf('66', plain,
% 0.35/0.52      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.35/0.52  thf('67', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (((k1_xboole_0) = (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0))
% 0.35/0.52          | ~ (v1_relat_1 @ X0)
% 0.35/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0)))),
% 0.35/0.52      inference('demod', [status(thm)], ['57', '65', '66'])).
% 0.35/0.52  thf('68', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ 
% 0.35/0.52             (k5_relat_1 @ 
% 0.35/0.52              (k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)) @ X1))
% 0.35/0.52          | ~ (v1_relat_1 @ X1)
% 0.35/0.52          | ((k1_xboole_0)
% 0.35/0.52              = (k5_relat_1 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X1)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['43', '67'])).
% 0.35/0.52  thf('69', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['33', '34'])).
% 0.35/0.52  thf('70', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf('71', plain,
% 0.35/0.52      (![X1 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X1))
% 0.35/0.52          | ~ (v1_relat_1 @ X1)
% 0.35/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X1)))),
% 0.35/0.52      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.35/0.52  thf('72', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X0)
% 0.35/0.52          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.35/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.35/0.52          | ~ (v1_relat_1 @ X0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['42', '71'])).
% 0.35/0.52  thf('73', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.35/0.52          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.35/0.52          | ~ (v1_relat_1 @ X0))),
% 0.35/0.52      inference('simplify', [status(thm)], ['72'])).
% 0.35/0.52  thf('74', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.35/0.52          | ~ (v1_relat_1 @ X0)
% 0.35/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['41', '73'])).
% 0.35/0.52  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.35/0.52  thf('76', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X0)
% 0.35/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.35/0.52      inference('demod', [status(thm)], ['74', '75'])).
% 0.35/0.52  thf('77', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (((k1_xboole_0) = (k5_relat_1 @ (k5_xboole_0 @ X0 @ X0) @ X1))
% 0.35/0.52          | ~ (v1_relat_1 @ X1))),
% 0.35/0.52      inference('sup+', [status(thm)], ['40', '76'])).
% 0.35/0.52  thf('78', plain,
% 0.35/0.52      (![X40 : $i, X41 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X40)
% 0.35/0.52          | ~ (v1_relat_1 @ X41)
% 0.35/0.52          | (v1_relat_1 @ (k5_relat_1 @ X40 @ X41)))),
% 0.35/0.52      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.35/0.52  thf('79', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         ((v1_relat_1 @ k1_xboole_0)
% 0.35/0.52          | ~ (v1_relat_1 @ X0)
% 0.35/0.52          | ~ (v1_relat_1 @ X0)
% 0.35/0.52          | ~ (v1_relat_1 @ (k5_xboole_0 @ X1 @ X1)))),
% 0.35/0.52      inference('sup+', [status(thm)], ['77', '78'])).
% 0.35/0.52  thf('80', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ (k5_xboole_0 @ X1 @ X1))
% 0.35/0.52          | ~ (v1_relat_1 @ X0)
% 0.35/0.52          | (v1_relat_1 @ k1_xboole_0))),
% 0.35/0.52      inference('simplify', [status(thm)], ['79'])).
% 0.35/0.52  thf('81', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0)) | (v1_relat_1 @ k1_xboole_0))),
% 0.35/0.52      inference('condensation', [status(thm)], ['80'])).
% 0.35/0.52  thf('82', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))
% 0.35/0.52          | (v1_relat_1 @ k1_xboole_0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['39', '81'])).
% 0.35/0.52  thf('83', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.35/0.52  thf('85', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['83', '84'])).
% 0.35/0.52  thf('86', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.35/0.52      inference('demod', [status(thm)], ['82', '85'])).
% 0.35/0.52  thf('87', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X0)
% 0.35/0.52          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.35/0.52          | ~ (v1_relat_1 @ X0))),
% 0.35/0.52      inference('demod', [status(thm)], ['38', '86'])).
% 0.35/0.52  thf('88', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.35/0.52          | ~ (v1_relat_1 @ X0))),
% 0.35/0.52      inference('simplify', [status(thm)], ['87'])).
% 0.35/0.52  thf('89', plain,
% 0.35/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.35/0.52  thf('90', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf('91', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.35/0.52           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['1', '4'])).
% 0.35/0.52  thf('92', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf(t62_relat_1, conjecture,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ A ) =>
% 0.35/0.52       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.35/0.52         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.35/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.52    (~( ![A:$i]:
% 0.35/0.52        ( ( v1_relat_1 @ A ) =>
% 0.35/0.52          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.35/0.52            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.35/0.52    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.35/0.52  thf('93', plain,
% 0.35/0.52      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.35/0.52        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('94', plain,
% 0.35/0.52      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.35/0.52         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['93'])).
% 0.35/0.52  thf('95', plain,
% 0.35/0.52      ((![X0 : $i]:
% 0.35/0.52          ((k5_relat_1 @ sk_A @ (k5_xboole_0 @ X0 @ X0)) != (k1_xboole_0)))
% 0.35/0.52         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['92', '94'])).
% 0.35/0.52  thf('96', plain,
% 0.35/0.52      ((![X0 : $i]:
% 0.35/0.52          ((k5_relat_1 @ sk_A @ 
% 0.35/0.52            (k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)))
% 0.35/0.52            != (k1_xboole_0)))
% 0.35/0.52         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['91', '95'])).
% 0.35/0.52  thf('97', plain,
% 0.35/0.52      ((![X0 : $i, X1 : $i]:
% 0.35/0.52          ((k5_relat_1 @ sk_A @ 
% 0.35/0.52            (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X1 @ X1)))
% 0.35/0.52            != (k1_xboole_0)))
% 0.35/0.52         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['90', '96'])).
% 0.35/0.52  thf('98', plain,
% 0.35/0.52      ((![X0 : $i]:
% 0.35/0.52          ((k5_relat_1 @ sk_A @ 
% 0.35/0.52            (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0)))
% 0.35/0.52            != (k1_xboole_0)))
% 0.35/0.52         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['89', '97'])).
% 0.35/0.52  thf('99', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.52  thf('100', plain,
% 0.35/0.52      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.35/0.52         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.35/0.52      inference('demod', [status(thm)], ['98', '99'])).
% 0.35/0.52  thf('101', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X0)
% 0.35/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.35/0.52      inference('demod', [status(thm)], ['74', '75'])).
% 0.35/0.52  thf('102', plain,
% 0.35/0.52      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.35/0.52         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['93'])).
% 0.35/0.52  thf('103', plain,
% 0.35/0.52      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.35/0.52         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['101', '102'])).
% 0.35/0.52  thf('104', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('105', plain,
% 0.35/0.52      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.35/0.52         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('demod', [status(thm)], ['103', '104'])).
% 0.35/0.52  thf('106', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.35/0.52      inference('simplify', [status(thm)], ['105'])).
% 0.35/0.52  thf('107', plain,
% 0.35/0.52      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.35/0.52       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.35/0.52      inference('split', [status(esa)], ['93'])).
% 0.35/0.52  thf('108', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.35/0.52      inference('sat_resolution*', [status(thm)], ['106', '107'])).
% 0.35/0.52  thf('109', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.35/0.52      inference('simpl_trail', [status(thm)], ['100', '108'])).
% 0.35/0.52  thf('110', plain,
% 0.35/0.52      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.35/0.52      inference('sup-', [status(thm)], ['88', '109'])).
% 0.35/0.52  thf('111', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('112', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.35/0.52      inference('demod', [status(thm)], ['110', '111'])).
% 0.35/0.52  thf('113', plain, ($false), inference('simplify', [status(thm)], ['112'])).
% 0.35/0.52  
% 0.35/0.52  % SZS output end Refutation
% 0.35/0.52  
% 0.35/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
