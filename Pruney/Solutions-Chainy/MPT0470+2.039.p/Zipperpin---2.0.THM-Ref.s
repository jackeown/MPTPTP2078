%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jFi1N7PuDM

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 259 expanded)
%              Number of leaves         :   27 (  93 expanded)
%              Depth                    :   25
%              Number of atoms          :  913 (1903 expanded)
%              Number of equality atoms :   94 ( 220 expanded)
%              Maximal formula depth    :   12 (   6 average)

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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
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

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X47 @ X46 ) ) @ ( k1_relat_1 @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('9',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('16',plain,(
    ! [X45: $i] :
      ( ( ( k3_xboole_0 @ X45 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X1 ) @ ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X1 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('18',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X36 @ X38 ) @ X37 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('24',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('27',plain,(
    ! [X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['17','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','27'])).

thf('29',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('30',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('31',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('32',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('33',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('34',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('39',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('40',plain,
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

thf('41',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X48 @ X49 ) )
        = ( k2_relat_1 @ X49 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','48'])).

thf('50',plain,(
    ! [X45: $i] :
      ( ( ( k3_xboole_0 @ X45 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('54',plain,(
    ! [X36: $i,X38: $i,X39: $i] :
      ( ( k2_zfmisc_1 @ X39 @ ( k4_xboole_0 @ X36 @ X38 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X39 @ X36 ) @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('57',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','58'])).

thf('60',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('64',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('67',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['62','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['31','69'])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','72'])).

thf('74',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','77'])).

thf('79',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

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

thf('85',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('88',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['85'])).

thf('89',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['85'])).

thf('94',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['86','94'])).

thf('96',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    $false ),
    inference(simplify,[status(thm)],['98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jFi1N7PuDM
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 280 iterations in 0.130s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.58  thf(dt_k5_relat_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.20/0.58       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      (![X43 : $i, X44 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X43)
% 0.20/0.58          | ~ (v1_relat_1 @ X44)
% 0.20/0.58          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.58  thf(cc1_relat_1, axiom,
% 0.20/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.20/0.58  thf('1', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.58  thf(t60_relat_1, axiom,
% 0.20/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.58  thf('2', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.58  thf(t44_relat_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( v1_relat_1 @ B ) =>
% 0.20/0.58           ( r1_tarski @
% 0.20/0.58             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (![X46 : $i, X47 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X46)
% 0.20/0.58          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X47 @ X46)) @ 
% 0.20/0.58             (k1_relat_1 @ X47))
% 0.20/0.58          | ~ (v1_relat_1 @ X47))),
% 0.20/0.58      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.20/0.58           k1_xboole_0)
% 0.20/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0)
% 0.20/0.58          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.20/0.58             k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.58  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.20/0.58             k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.58  thf(t92_xboole_1, axiom,
% 0.20/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.58  thf('8', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.58  thf('9', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.58  thf('10', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.20/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.58  thf(d10_xboole_0, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      (![X1 : $i, X3 : $i]:
% 0.20/0.58         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.20/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ X1 @ X1))
% 0.20/0.58          | ((X0) = (k5_xboole_0 @ X1 @ X1)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ X1 @ k1_xboole_0) | ((X1) = (k5_xboole_0 @ X0 @ X0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['8', '13'])).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.58              = (k5_xboole_0 @ X1 @ X1)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['7', '14'])).
% 0.20/0.58  thf(t22_relat_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) =>
% 0.20/0.58       ( ( k3_xboole_0 @
% 0.20/0.58           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.20/0.58         ( A ) ) ))).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      (![X45 : $i]:
% 0.20/0.58         (((k3_xboole_0 @ X45 @ 
% 0.20/0.58            (k2_zfmisc_1 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))) = (
% 0.20/0.58            X45))
% 0.20/0.58          | ~ (v1_relat_1 @ X45))),
% 0.20/0.58      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X1) @ 
% 0.20/0.58            (k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ 
% 0.20/0.58             (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X1))))
% 0.20/0.58            = (k5_relat_1 @ k1_xboole_0 @ X1))
% 0.20/0.58          | ~ (v1_relat_1 @ X1)
% 0.20/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X1)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.58  thf(t125_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.20/0.58         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.20/0.58       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.58         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.58         ((k2_zfmisc_1 @ (k4_xboole_0 @ X36 @ X38) @ X37)
% 0.20/0.58           = (k4_xboole_0 @ (k2_zfmisc_1 @ X36 @ X37) @ 
% 0.20/0.58              (k2_zfmisc_1 @ X38 @ X37)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.20/0.58  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.58  thf('19', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.58      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.58  thf(t100_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      (![X4 : $i, X5 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ X4 @ X5)
% 0.20/0.58           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.58  thf('21', plain,
% 0.20/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.20/0.58           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['18', '21'])).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.58  thf('24', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.58  thf('25', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.20/0.58  thf(t2_boole, axiom,
% 0.20/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.58  thf('27', plain,
% 0.20/0.58      (![X1 : $i]:
% 0.20/0.58         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X1))
% 0.20/0.58          | ~ (v1_relat_1 @ X1)
% 0.20/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X1)))),
% 0.20/0.58      inference('demod', [status(thm)], ['17', '25', '26'])).
% 0.20/0.58  thf('28', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0)
% 0.20/0.58          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['0', '27'])).
% 0.20/0.58  thf('29', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.58  thf('30', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.58  thf('31', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      (![X43 : $i, X44 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X43)
% 0.20/0.58          | ~ (v1_relat_1 @ X44)
% 0.20/0.58          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.58  thf('33', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.58  thf('35', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      (![X4 : $i, X5 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ X4 @ X5)
% 0.20/0.58           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.58  thf('37', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.20/0.58           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.58  thf('38', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.58  thf('39', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.58  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.58  thf(t47_relat_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( v1_relat_1 @ B ) =>
% 0.20/0.58           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.58             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      (![X48 : $i, X49 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X48)
% 0.20/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X48 @ X49)) = (k2_relat_1 @ X49))
% 0.20/0.58          | ~ (r1_tarski @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X48))
% 0.20/0.58          | ~ (v1_relat_1 @ X49))),
% 0.20/0.58      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.20/0.58  thf('42', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.20/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.58              = (k2_relat_1 @ k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.58  thf('43', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.58  thf('44', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.58  thf('45', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.20/0.58  thf('46', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0)
% 0.20/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['39', '45'])).
% 0.20/0.58  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.58  thf('48', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.58  thf('49', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (((k2_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 0.20/0.58            = (k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ X1))),
% 0.20/0.58      inference('sup+', [status(thm)], ['38', '48'])).
% 0.20/0.58  thf('50', plain,
% 0.20/0.58      (![X45 : $i]:
% 0.20/0.58         (((k3_xboole_0 @ X45 @ 
% 0.20/0.58            (k2_zfmisc_1 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))) = (
% 0.20/0.58            X45))
% 0.20/0.58          | ~ (v1_relat_1 @ X45))),
% 0.20/0.58      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.20/0.58  thf('51', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (((k3_xboole_0 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ 
% 0.20/0.58            (k2_zfmisc_1 @ 
% 0.20/0.58             (k1_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0))) @ 
% 0.20/0.58             k1_xboole_0))
% 0.20/0.58            = (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 0.20/0.58          | ~ (v1_relat_1 @ X1)
% 0.20/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.58  thf('52', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.58  thf('53', plain,
% 0.20/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.58  thf('54', plain,
% 0.20/0.58      (![X36 : $i, X38 : $i, X39 : $i]:
% 0.20/0.58         ((k2_zfmisc_1 @ X39 @ (k4_xboole_0 @ X36 @ X38))
% 0.20/0.58           = (k4_xboole_0 @ (k2_zfmisc_1 @ X39 @ X36) @ 
% 0.20/0.58              (k2_zfmisc_1 @ X39 @ X38)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.20/0.58  thf('55', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.20/0.58           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['53', '54'])).
% 0.20/0.58  thf('56', plain,
% 0.20/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.58  thf('57', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.58  thf('58', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.58  thf('59', plain,
% 0.20/0.58      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['52', '58'])).
% 0.20/0.58  thf('60', plain,
% 0.20/0.58      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.58  thf('61', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (((k1_xboole_0) = (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 0.20/0.58          | ~ (v1_relat_1 @ X1)
% 0.20/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0))))),
% 0.20/0.58      inference('demod', [status(thm)], ['51', '59', '60'])).
% 0.20/0.58  thf('62', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ 
% 0.20/0.58             (k5_relat_1 @ X1 @ 
% 0.20/0.58              (k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))))
% 0.20/0.58          | ~ (v1_relat_1 @ X1)
% 0.20/0.58          | ((k1_xboole_0)
% 0.20/0.58              = (k5_relat_1 @ X1 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['37', '61'])).
% 0.20/0.58  thf('63', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.20/0.58           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.58  thf('64', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.58  thf('65', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['63', '64'])).
% 0.20/0.58  thf('66', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.58  thf('67', plain,
% 0.20/0.58      (![X1 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ X1)
% 0.20/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['62', '65', '66'])).
% 0.20/0.58  thf('68', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0)
% 0.20/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['32', '67'])).
% 0.20/0.58  thf('69', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ X0)
% 0.20/0.58          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.58  thf('70', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0)
% 0.20/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['31', '69'])).
% 0.20/0.58  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.58  thf('72', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['70', '71'])).
% 0.20/0.58  thf('73', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (((k1_xboole_0) = (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 0.20/0.58          | ~ (v1_relat_1 @ X1))),
% 0.20/0.58      inference('sup+', [status(thm)], ['30', '72'])).
% 0.20/0.58  thf('74', plain,
% 0.20/0.58      (![X43 : $i, X44 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X43)
% 0.20/0.58          | ~ (v1_relat_1 @ X44)
% 0.20/0.58          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.58  thf('75', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((v1_relat_1 @ k1_xboole_0)
% 0.20/0.58          | ~ (v1_relat_1 @ X1)
% 0.20/0.58          | ~ (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0))
% 0.20/0.58          | ~ (v1_relat_1 @ X1))),
% 0.20/0.58      inference('sup+', [status(thm)], ['73', '74'])).
% 0.20/0.58  thf('76', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0))
% 0.20/0.58          | ~ (v1_relat_1 @ X1)
% 0.20/0.58          | (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['75'])).
% 0.20/0.58  thf('77', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0)) | (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.58      inference('condensation', [status(thm)], ['76'])).
% 0.20/0.58  thf('78', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))
% 0.20/0.58          | (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['29', '77'])).
% 0.20/0.58  thf('79', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.58  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.58  thf('81', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['79', '80'])).
% 0.20/0.58  thf('82', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.58      inference('demod', [status(thm)], ['78', '81'])).
% 0.20/0.58  thf('83', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0)
% 0.20/0.58          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['28', '82'])).
% 0.20/0.58  thf('84', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['83'])).
% 0.20/0.58  thf(t62_relat_1, conjecture,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) =>
% 0.20/0.58       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.20/0.58         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i]:
% 0.20/0.58        ( ( v1_relat_1 @ A ) =>
% 0.20/0.58          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.20/0.58            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.20/0.58  thf('85', plain,
% 0.20/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.20/0.58        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('86', plain,
% 0.20/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.20/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('split', [status(esa)], ['85'])).
% 0.20/0.58  thf('87', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['70', '71'])).
% 0.20/0.58  thf('88', plain,
% 0.20/0.58      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.58      inference('split', [status(esa)], ['85'])).
% 0.20/0.58  thf('89', plain,
% 0.20/0.58      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.20/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.58  thf('90', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('91', plain,
% 0.20/0.58      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.58      inference('demod', [status(thm)], ['89', '90'])).
% 0.20/0.58  thf('92', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.58      inference('simplify', [status(thm)], ['91'])).
% 0.20/0.58  thf('93', plain,
% 0.20/0.58      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.58       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.58      inference('split', [status(esa)], ['85'])).
% 0.20/0.58  thf('94', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 0.20/0.58  thf('95', plain, (((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['86', '94'])).
% 0.20/0.58  thf('96', plain,
% 0.20/0.58      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['84', '95'])).
% 0.20/0.58  thf('97', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('98', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['96', '97'])).
% 0.20/0.58  thf('99', plain, ($false), inference('simplify', [status(thm)], ['98'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
