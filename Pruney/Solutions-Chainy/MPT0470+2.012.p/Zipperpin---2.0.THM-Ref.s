%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wQALqSaEZU

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:27 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  163 (4037 expanded)
%              Number of leaves         :   27 (1338 expanded)
%              Depth                    :   48
%              Number of atoms          : 1057 (24785 expanded)
%              Number of equality atoms :  105 (2715 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ~ ( v1_relat_1 @ X40 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X37: $i] :
      ( ( v1_relat_1 @ X37 )
      | ~ ( v1_xboole_0 @ X37 ) ) ),
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

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X43: $i] :
      ( ( ( k1_relat_1 @ X43 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X34 ) )
      | ~ ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('7',plain,(
    ! [X42: $i] :
      ( ( ( k3_xboole_0 @ X42 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X42 ) @ ( k2_relat_1 @ X42 ) ) )
        = X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,
    ( ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X38: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X47 @ X46 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X46 ) @ ( k4_relat_1 @ X47 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('27',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X38: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X37: $i] :
      ( ( v1_relat_1 @ X37 )
      | ~ ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['33'])).

thf('35',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','37'])).

thf('39',plain,(
    ! [X38: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('41',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ~ ( v1_relat_1 @ X40 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('44',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('45',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X47 @ X46 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X46 ) @ ( k4_relat_1 @ X47 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('51',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('54',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('56',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X45 @ X44 ) ) @ ( k2_relat_1 @ X44 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) @ ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('59',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('60',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63','64'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('66',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X45 @ X44 ) ) @ ( k2_relat_1 @ X44 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('74',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ~ ( v1_relat_1 @ X40 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('77',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','78'])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,(
    v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','68'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('85',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('87',plain,(
    v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('88',plain,
    ( k1_xboole_0
    = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','95'])).

thf('97',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','101'])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('106',plain,(
    ! [X41: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X41 ) )
        = X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','109'])).

thf('111',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
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

thf('115',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['114','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('120',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['115'])).

thf('121',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('125',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['115'])).

thf('128',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['117','128'])).

thf('130',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('133',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    $false ),
    inference(simplify,[status(thm)],['133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wQALqSaEZU
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 21:03:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.10/1.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.10/1.29  % Solved by: fo/fo7.sh
% 1.10/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.10/1.29  % done 1271 iterations in 0.828s
% 1.10/1.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.10/1.29  % SZS output start Refutation
% 1.10/1.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.10/1.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.10/1.29  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.10/1.29  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.10/1.29  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.10/1.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.10/1.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.10/1.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.10/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.10/1.29  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.10/1.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.10/1.29  thf(dt_k5_relat_1, axiom,
% 1.10/1.29    (![A:$i,B:$i]:
% 1.10/1.29     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.10/1.29       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.10/1.29  thf('0', plain,
% 1.10/1.29      (![X39 : $i, X40 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X39)
% 1.10/1.29          | ~ (v1_relat_1 @ X40)
% 1.10/1.29          | (v1_relat_1 @ (k5_relat_1 @ X39 @ X40)))),
% 1.10/1.29      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.10/1.29  thf(cc1_relat_1, axiom,
% 1.10/1.29    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 1.10/1.29  thf('1', plain, (![X37 : $i]: ((v1_relat_1 @ X37) | ~ (v1_xboole_0 @ X37))),
% 1.10/1.29      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.10/1.29  thf(t60_relat_1, axiom,
% 1.10/1.29    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.10/1.29     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.10/1.29  thf('2', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.10/1.29      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.10/1.29  thf(t37_relat_1, axiom,
% 1.10/1.29    (![A:$i]:
% 1.10/1.29     ( ( v1_relat_1 @ A ) =>
% 1.10/1.29       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.10/1.29         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.10/1.29  thf('3', plain,
% 1.10/1.29      (![X43 : $i]:
% 1.10/1.29         (((k1_relat_1 @ X43) = (k2_relat_1 @ (k4_relat_1 @ X43)))
% 1.10/1.29          | ~ (v1_relat_1 @ X43))),
% 1.10/1.29      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.10/1.29  thf(fc3_zfmisc_1, axiom,
% 1.10/1.29    (![A:$i,B:$i]:
% 1.10/1.29     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 1.10/1.29  thf('4', plain,
% 1.10/1.29      (![X33 : $i, X34 : $i]:
% 1.10/1.29         ((v1_xboole_0 @ (k2_zfmisc_1 @ X33 @ X34)) | ~ (v1_xboole_0 @ X34))),
% 1.10/1.29      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 1.10/1.29  thf(l13_xboole_0, axiom,
% 1.10/1.29    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.10/1.29  thf('5', plain,
% 1.10/1.29      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.10/1.29  thf('6', plain,
% 1.10/1.29      (![X0 : $i, X1 : $i]:
% 1.10/1.29         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['4', '5'])).
% 1.10/1.29  thf(t22_relat_1, axiom,
% 1.10/1.29    (![A:$i]:
% 1.10/1.29     ( ( v1_relat_1 @ A ) =>
% 1.10/1.29       ( ( k3_xboole_0 @
% 1.10/1.29           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 1.10/1.29         ( A ) ) ))).
% 1.10/1.29  thf('7', plain,
% 1.10/1.29      (![X42 : $i]:
% 1.10/1.29         (((k3_xboole_0 @ X42 @ 
% 1.10/1.29            (k2_zfmisc_1 @ (k1_relat_1 @ X42) @ (k2_relat_1 @ X42))) = (
% 1.10/1.29            X42))
% 1.10/1.29          | ~ (v1_relat_1 @ X42))),
% 1.10/1.29      inference('cnf', [status(esa)], [t22_relat_1])).
% 1.10/1.29  thf('8', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 1.10/1.29          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['6', '7'])).
% 1.10/1.29  thf(t2_boole, axiom,
% 1.10/1.29    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.10/1.29  thf('9', plain,
% 1.10/1.29      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.10/1.29      inference('cnf', [status(esa)], [t2_boole])).
% 1.10/1.29  thf('10', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k1_xboole_0) = (X0))
% 1.10/1.29          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('demod', [status(thm)], ['8', '9'])).
% 1.10/1.29  thf('11', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0)
% 1.10/1.29          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 1.10/1.29          | ((k1_xboole_0) = (k4_relat_1 @ X0)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['3', '10'])).
% 1.10/1.29  thf('12', plain,
% 1.10/1.29      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.10/1.29        | ((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 1.10/1.29        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 1.10/1.29        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.10/1.29      inference('sup-', [status(thm)], ['2', '11'])).
% 1.10/1.29  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.10/1.29  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.10/1.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.10/1.29  thf('14', plain,
% 1.10/1.29      ((((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 1.10/1.29        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 1.10/1.29        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.10/1.29      inference('demod', [status(thm)], ['12', '13'])).
% 1.10/1.29  thf(dt_k4_relat_1, axiom,
% 1.10/1.29    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 1.10/1.29  thf('15', plain,
% 1.10/1.29      (![X38 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X38)) | ~ (v1_relat_1 @ X38))),
% 1.10/1.29      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.10/1.29  thf('16', plain,
% 1.10/1.29      ((~ (v1_relat_1 @ k1_xboole_0)
% 1.10/1.29        | ((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0)))),
% 1.10/1.29      inference('clc', [status(thm)], ['14', '15'])).
% 1.10/1.29  thf('17', plain,
% 1.10/1.29      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.10/1.29        | ((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['1', '16'])).
% 1.10/1.29  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.10/1.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.10/1.29  thf('19', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.10/1.29      inference('demod', [status(thm)], ['17', '18'])).
% 1.10/1.29  thf(t54_relat_1, axiom,
% 1.10/1.29    (![A:$i]:
% 1.10/1.29     ( ( v1_relat_1 @ A ) =>
% 1.10/1.29       ( ![B:$i]:
% 1.10/1.29         ( ( v1_relat_1 @ B ) =>
% 1.10/1.29           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.10/1.29             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 1.10/1.29  thf('20', plain,
% 1.10/1.29      (![X46 : $i, X47 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X46)
% 1.10/1.29          | ((k4_relat_1 @ (k5_relat_1 @ X47 @ X46))
% 1.10/1.29              = (k5_relat_1 @ (k4_relat_1 @ X46) @ (k4_relat_1 @ X47)))
% 1.10/1.29          | ~ (v1_relat_1 @ X47))),
% 1.10/1.29      inference('cnf', [status(esa)], [t54_relat_1])).
% 1.10/1.29  thf('21', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.10/1.29            = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0))
% 1.10/1.29          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['19', '20'])).
% 1.10/1.29  thf('22', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.10/1.29      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.10/1.29  thf('23', plain,
% 1.10/1.29      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.10/1.29  thf('24', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.10/1.29      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.10/1.29  thf('25', plain,
% 1.10/1.29      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['23', '24'])).
% 1.10/1.29  thf('26', plain,
% 1.10/1.29      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.10/1.29  thf('27', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.10/1.29      inference('demod', [status(thm)], ['17', '18'])).
% 1.10/1.29  thf('28', plain,
% 1.10/1.29      (![X0 : $i]: (((k1_xboole_0) = (k4_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['26', '27'])).
% 1.10/1.29  thf('29', plain,
% 1.10/1.29      (![X38 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X38)) | ~ (v1_relat_1 @ X38))),
% 1.10/1.29      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.10/1.29  thf('30', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         ((v1_relat_1 @ k1_xboole_0)
% 1.10/1.29          | ~ (v1_xboole_0 @ X0)
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['28', '29'])).
% 1.10/1.29  thf('31', plain, (![X37 : $i]: ((v1_relat_1 @ X37) | ~ (v1_xboole_0 @ X37))),
% 1.10/1.29      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.10/1.29  thf('32', plain,
% 1.10/1.29      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 1.10/1.29      inference('clc', [status(thm)], ['30', '31'])).
% 1.10/1.29  thf('33', plain,
% 1.10/1.29      (![X0 : $i, X1 : $i]:
% 1.10/1.29         ((v1_relat_1 @ (k2_relat_1 @ X0))
% 1.10/1.29          | ~ (v1_xboole_0 @ X0)
% 1.10/1.29          | ~ (v1_xboole_0 @ X1))),
% 1.10/1.29      inference('sup+', [status(thm)], ['25', '32'])).
% 1.10/1.29  thf('34', plain,
% 1.10/1.29      (![X0 : $i]: ((v1_relat_1 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('condensation', [status(thm)], ['33'])).
% 1.10/1.29  thf('35', plain,
% 1.10/1.29      (((v1_relat_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['22', '34'])).
% 1.10/1.29  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.10/1.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.10/1.29  thf('37', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.10/1.29      inference('demod', [status(thm)], ['35', '36'])).
% 1.10/1.29  thf('38', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.10/1.29            = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('demod', [status(thm)], ['21', '37'])).
% 1.10/1.29  thf('39', plain,
% 1.10/1.29      (![X38 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X38)) | ~ (v1_relat_1 @ X38))),
% 1.10/1.29      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.10/1.29  thf('40', plain,
% 1.10/1.29      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.10/1.29  thf('41', plain,
% 1.10/1.29      (![X39 : $i, X40 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X39)
% 1.10/1.29          | ~ (v1_relat_1 @ X40)
% 1.10/1.29          | (v1_relat_1 @ (k5_relat_1 @ X39 @ X40)))),
% 1.10/1.29      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.10/1.29  thf('42', plain,
% 1.10/1.29      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.10/1.29  thf('43', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.10/1.29      inference('demod', [status(thm)], ['17', '18'])).
% 1.10/1.29  thf('44', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.10/1.29      inference('demod', [status(thm)], ['17', '18'])).
% 1.10/1.29  thf('45', plain,
% 1.10/1.29      (![X46 : $i, X47 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X46)
% 1.10/1.29          | ((k4_relat_1 @ (k5_relat_1 @ X47 @ X46))
% 1.10/1.29              = (k5_relat_1 @ (k4_relat_1 @ X46) @ (k4_relat_1 @ X47)))
% 1.10/1.29          | ~ (v1_relat_1 @ X47))),
% 1.10/1.29      inference('cnf', [status(esa)], [t54_relat_1])).
% 1.10/1.29  thf('46', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.10/1.29            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 1.10/1.29          | ~ (v1_relat_1 @ X0)
% 1.10/1.29          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['44', '45'])).
% 1.10/1.29  thf('47', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.10/1.29      inference('demod', [status(thm)], ['35', '36'])).
% 1.10/1.29  thf('48', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.10/1.29            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('demod', [status(thm)], ['46', '47'])).
% 1.10/1.29  thf('49', plain,
% 1.10/1.29      ((((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.10/1.29          = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.10/1.29        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['43', '48'])).
% 1.10/1.29  thf('50', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.10/1.29      inference('demod', [status(thm)], ['35', '36'])).
% 1.10/1.29  thf('51', plain,
% 1.10/1.29      (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.10/1.29         = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 1.10/1.29      inference('demod', [status(thm)], ['49', '50'])).
% 1.10/1.29  thf('52', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.10/1.29            = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.10/1.29          | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['42', '51'])).
% 1.10/1.29  thf('53', plain,
% 1.10/1.29      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.10/1.29  thf('54', plain,
% 1.10/1.29      (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.10/1.29         = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 1.10/1.29      inference('demod', [status(thm)], ['49', '50'])).
% 1.10/1.29  thf('55', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.10/1.29            = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.10/1.29          | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['53', '54'])).
% 1.10/1.29  thf(t45_relat_1, axiom,
% 1.10/1.29    (![A:$i]:
% 1.10/1.29     ( ( v1_relat_1 @ A ) =>
% 1.10/1.29       ( ![B:$i]:
% 1.10/1.29         ( ( v1_relat_1 @ B ) =>
% 1.10/1.29           ( r1_tarski @
% 1.10/1.29             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 1.10/1.29  thf('56', plain,
% 1.10/1.29      (![X44 : $i, X45 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X44)
% 1.10/1.29          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X45 @ X44)) @ 
% 1.10/1.29             (k2_relat_1 @ X44))
% 1.10/1.29          | ~ (v1_relat_1 @ X45))),
% 1.10/1.29      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.10/1.29  thf('57', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         ((r1_tarski @ 
% 1.10/1.29           (k2_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))) @ 
% 1.10/1.29           (k2_relat_1 @ k1_xboole_0))
% 1.10/1.29          | ~ (v1_xboole_0 @ X0)
% 1.10/1.29          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.10/1.29          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['55', '56'])).
% 1.10/1.29  thf('58', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.10/1.29      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.10/1.29  thf('59', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.10/1.29      inference('demod', [status(thm)], ['35', '36'])).
% 1.10/1.29  thf('60', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.10/1.29      inference('demod', [status(thm)], ['35', '36'])).
% 1.10/1.29  thf('61', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         ((r1_tarski @ 
% 1.10/1.29           (k2_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))) @ 
% 1.10/1.29           k1_xboole_0)
% 1.10/1.29          | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 1.10/1.29  thf('62', plain,
% 1.10/1.29      (((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)) @ 
% 1.10/1.29         k1_xboole_0)
% 1.10/1.29        | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.10/1.29        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['52', '61'])).
% 1.10/1.29  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.10/1.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.10/1.29  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.10/1.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.10/1.29  thf('65', plain,
% 1.10/1.29      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)) @ 
% 1.10/1.29        k1_xboole_0)),
% 1.10/1.29      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.10/1.29  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.10/1.29  thf('66', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.10/1.29      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.10/1.29  thf(d10_xboole_0, axiom,
% 1.10/1.29    (![A:$i,B:$i]:
% 1.10/1.29     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.10/1.29  thf('67', plain,
% 1.10/1.29      (![X1 : $i, X3 : $i]:
% 1.10/1.29         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.10/1.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.10/1.29  thf('68', plain,
% 1.10/1.29      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['66', '67'])).
% 1.10/1.29  thf('69', plain,
% 1.10/1.29      (((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.10/1.29      inference('sup-', [status(thm)], ['65', '68'])).
% 1.10/1.29  thf('70', plain,
% 1.10/1.29      (![X44 : $i, X45 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X44)
% 1.10/1.29          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X45 @ X44)) @ 
% 1.10/1.29             (k2_relat_1 @ X44))
% 1.10/1.29          | ~ (v1_relat_1 @ X45))),
% 1.10/1.29      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.10/1.29  thf('71', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         ((r1_tarski @ 
% 1.10/1.29           (k2_relat_1 @ 
% 1.10/1.29            (k5_relat_1 @ X0 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))) @ 
% 1.10/1.29           k1_xboole_0)
% 1.10/1.29          | ~ (v1_relat_1 @ X0)
% 1.10/1.29          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.10/1.29      inference('sup+', [status(thm)], ['69', '70'])).
% 1.10/1.29  thf('72', plain,
% 1.10/1.29      (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.10/1.29         = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 1.10/1.29      inference('demod', [status(thm)], ['49', '50'])).
% 1.10/1.29  thf('73', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.10/1.29            = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.10/1.29          | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['53', '54'])).
% 1.10/1.29  thf('74', plain,
% 1.10/1.29      (![X39 : $i, X40 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X39)
% 1.10/1.29          | ~ (v1_relat_1 @ X40)
% 1.10/1.29          | (v1_relat_1 @ (k5_relat_1 @ X39 @ X40)))),
% 1.10/1.29      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.10/1.29  thf('75', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.10/1.29          | ~ (v1_xboole_0 @ X0)
% 1.10/1.29          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.10/1.29          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['73', '74'])).
% 1.10/1.29  thf('76', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.10/1.29      inference('demod', [status(thm)], ['35', '36'])).
% 1.10/1.29  thf('77', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.10/1.29      inference('demod', [status(thm)], ['35', '36'])).
% 1.10/1.29  thf('78', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.10/1.29          | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.10/1.29  thf('79', plain,
% 1.10/1.29      (((v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.10/1.29        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['72', '78'])).
% 1.10/1.29  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.10/1.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.10/1.29  thf('81', plain, ((v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 1.10/1.29      inference('demod', [status(thm)], ['79', '80'])).
% 1.10/1.29  thf('82', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         ((r1_tarski @ 
% 1.10/1.29           (k2_relat_1 @ 
% 1.10/1.29            (k5_relat_1 @ X0 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))) @ 
% 1.10/1.29           k1_xboole_0)
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('demod', [status(thm)], ['71', '81'])).
% 1.10/1.29  thf('83', plain,
% 1.10/1.29      (((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.10/1.29      inference('sup-', [status(thm)], ['65', '68'])).
% 1.10/1.29  thf('84', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k1_xboole_0) = (X0))
% 1.10/1.29          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('demod', [status(thm)], ['8', '9'])).
% 1.10/1.29  thf('85', plain,
% 1.10/1.29      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.10/1.29        | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.10/1.29        | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['83', '84'])).
% 1.10/1.29  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.10/1.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.10/1.29  thf('87', plain, ((v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 1.10/1.29      inference('demod', [status(thm)], ['79', '80'])).
% 1.10/1.29  thf('88', plain,
% 1.10/1.29      (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 1.10/1.29      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.10/1.29  thf('89', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.10/1.29           k1_xboole_0)
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('demod', [status(thm)], ['82', '88'])).
% 1.10/1.29  thf('90', plain,
% 1.10/1.29      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['66', '67'])).
% 1.10/1.29  thf('91', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X0)
% 1.10/1.29          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['89', '90'])).
% 1.10/1.29  thf('92', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k1_xboole_0) = (X0))
% 1.10/1.29          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('demod', [status(thm)], ['8', '9'])).
% 1.10/1.29  thf('93', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.10/1.29          | ~ (v1_relat_1 @ X0)
% 1.10/1.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.10/1.29          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['91', '92'])).
% 1.10/1.29  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.10/1.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.10/1.29  thf('95', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X0)
% 1.10/1.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.10/1.29          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.10/1.29      inference('demod', [status(thm)], ['93', '94'])).
% 1.10/1.29  thf('96', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ k1_xboole_0)
% 1.10/1.29          | ~ (v1_relat_1 @ X0)
% 1.10/1.29          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('sup-', [status(thm)], ['41', '95'])).
% 1.10/1.29  thf('97', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.10/1.29      inference('demod', [status(thm)], ['35', '36'])).
% 1.10/1.29  thf('98', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X0)
% 1.10/1.29          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('demod', [status(thm)], ['96', '97'])).
% 1.10/1.29  thf('99', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('simplify', [status(thm)], ['98'])).
% 1.10/1.29  thf('100', plain,
% 1.10/1.29      (![X0 : $i, X1 : $i]:
% 1.10/1.29         (((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 1.10/1.29          | ~ (v1_xboole_0 @ X0)
% 1.10/1.29          | ~ (v1_relat_1 @ X1))),
% 1.10/1.29      inference('sup+', [status(thm)], ['40', '99'])).
% 1.10/1.29  thf('101', plain,
% 1.10/1.29      (![X0 : $i, X1 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X0)
% 1.10/1.29          | ~ (v1_xboole_0 @ X1)
% 1.10/1.29          | ((k1_xboole_0) = (k5_relat_1 @ (k4_relat_1 @ X0) @ X1)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['39', '100'])).
% 1.10/1.29  thf('102', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 1.10/1.29          | ~ (v1_relat_1 @ X0)
% 1.10/1.29          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['38', '101'])).
% 1.10/1.29  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.10/1.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.10/1.29  thf('104', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 1.10/1.29          | ~ (v1_relat_1 @ X0)
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('demod', [status(thm)], ['102', '103'])).
% 1.10/1.29  thf('105', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X0)
% 1.10/1.29          | ((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 1.10/1.29      inference('simplify', [status(thm)], ['104'])).
% 1.10/1.29  thf(involutiveness_k4_relat_1, axiom,
% 1.10/1.29    (![A:$i]:
% 1.10/1.29     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 1.10/1.29  thf('106', plain,
% 1.10/1.29      (![X41 : $i]:
% 1.10/1.29         (((k4_relat_1 @ (k4_relat_1 @ X41)) = (X41)) | ~ (v1_relat_1 @ X41))),
% 1.10/1.29      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 1.10/1.29  thf('107', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0)
% 1.10/1.29          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.10/1.29      inference('sup+', [status(thm)], ['105', '106'])).
% 1.10/1.29  thf('108', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.10/1.29      inference('demod', [status(thm)], ['17', '18'])).
% 1.10/1.29  thf('109', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0)
% 1.10/1.29          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.10/1.29      inference('demod', [status(thm)], ['107', '108'])).
% 1.10/1.29  thf('110', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X0)
% 1.10/1.29          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.10/1.29          | ~ (v1_relat_1 @ X0)
% 1.10/1.29          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['0', '109'])).
% 1.10/1.29  thf('111', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.10/1.29      inference('demod', [status(thm)], ['35', '36'])).
% 1.10/1.29  thf('112', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X0)
% 1.10/1.29          | ~ (v1_relat_1 @ X0)
% 1.10/1.29          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.10/1.29      inference('demod', [status(thm)], ['110', '111'])).
% 1.10/1.29  thf('113', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('simplify', [status(thm)], ['112'])).
% 1.10/1.29  thf('114', plain,
% 1.10/1.29      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.10/1.29  thf(t62_relat_1, conjecture,
% 1.10/1.29    (![A:$i]:
% 1.10/1.29     ( ( v1_relat_1 @ A ) =>
% 1.10/1.29       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.10/1.29         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 1.10/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.10/1.29    (~( ![A:$i]:
% 1.10/1.29        ( ( v1_relat_1 @ A ) =>
% 1.10/1.29          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.10/1.29            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 1.10/1.29    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 1.10/1.29  thf('115', plain,
% 1.10/1.29      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 1.10/1.29        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 1.10/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.29  thf('116', plain,
% 1.10/1.29      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 1.10/1.29         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.10/1.29      inference('split', [status(esa)], ['115'])).
% 1.10/1.29  thf('117', plain,
% 1.10/1.29      ((![X0 : $i]:
% 1.10/1.29          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.10/1.29         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.10/1.29      inference('sup-', [status(thm)], ['114', '116'])).
% 1.10/1.29  thf('118', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('simplify', [status(thm)], ['98'])).
% 1.10/1.29  thf('119', plain,
% 1.10/1.29      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.10/1.29  thf('120', plain,
% 1.10/1.29      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 1.10/1.29         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.10/1.29      inference('split', [status(esa)], ['115'])).
% 1.10/1.29  thf('121', plain,
% 1.10/1.29      ((![X0 : $i]:
% 1.10/1.29          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.10/1.29         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.10/1.29      inference('sup-', [status(thm)], ['119', '120'])).
% 1.10/1.29  thf('122', plain,
% 1.10/1.29      (((((k1_xboole_0) != (k1_xboole_0))
% 1.10/1.29         | ~ (v1_relat_1 @ sk_A)
% 1.10/1.29         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.10/1.29         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.10/1.29      inference('sup-', [status(thm)], ['118', '121'])).
% 1.10/1.29  thf('123', plain, ((v1_relat_1 @ sk_A)),
% 1.10/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.29  thf('124', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.10/1.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.10/1.29  thf('125', plain,
% 1.10/1.29      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.10/1.29         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.10/1.29      inference('demod', [status(thm)], ['122', '123', '124'])).
% 1.10/1.29  thf('126', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 1.10/1.29      inference('simplify', [status(thm)], ['125'])).
% 1.10/1.29  thf('127', plain,
% 1.10/1.29      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 1.10/1.29       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 1.10/1.29      inference('split', [status(esa)], ['115'])).
% 1.10/1.29  thf('128', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.10/1.29      inference('sat_resolution*', [status(thm)], ['126', '127'])).
% 1.10/1.29  thf('129', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.10/1.29      inference('simpl_trail', [status(thm)], ['117', '128'])).
% 1.10/1.29  thf('130', plain,
% 1.10/1.29      ((((k1_xboole_0) != (k1_xboole_0))
% 1.10/1.29        | ~ (v1_relat_1 @ sk_A)
% 1.10/1.29        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.10/1.29      inference('sup-', [status(thm)], ['113', '129'])).
% 1.10/1.29  thf('131', plain, ((v1_relat_1 @ sk_A)),
% 1.10/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.29  thf('132', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.10/1.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.10/1.29  thf('133', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.10/1.29      inference('demod', [status(thm)], ['130', '131', '132'])).
% 1.10/1.29  thf('134', plain, ($false), inference('simplify', [status(thm)], ['133'])).
% 1.10/1.29  
% 1.10/1.29  % SZS output end Refutation
% 1.10/1.29  
% 1.10/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
