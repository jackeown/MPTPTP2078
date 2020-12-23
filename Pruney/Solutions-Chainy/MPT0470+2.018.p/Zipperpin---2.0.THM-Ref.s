%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZejZoiS6jH

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:28 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 534 expanded)
%              Number of leaves         :   30 ( 182 expanded)
%              Depth                    :   32
%              Number of atoms          :  854 (3809 expanded)
%              Number of equality atoms :   78 ( 320 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X47: $i] :
      ( ( ( k2_relat_1 @ X47 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X47 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X46: $i] :
      ( ( r1_tarski @ X46 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X46 ) @ ( k2_relat_1 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X42 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_tarski @ ( k4_relat_1 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X35 @ X37 ) @ X36 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X35 @ X36 ) @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('15',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','16'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('18',plain,(
    ! [X41: $i] :
      ( ( v1_relat_1 @ X41 )
      | ~ ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('19',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('20',plain,(
    ! [X41: $i] :
      ( ( v1_relat_1 @ X41 )
      | ~ ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('21',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('22',plain,(
    ! [X41: $i] :
      ( ( v1_relat_1 @ X41 )
      | ~ ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('23',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('24',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X49 @ X48 ) ) @ ( k2_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X46: $i] :
      ( ( r1_tarski @ X46 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X46 ) @ ( k2_relat_1 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('36',plain,(
    ! [X35: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ X38 @ ( k4_xboole_0 @ X35 @ X37 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X38 @ X35 ) @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('40',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['34','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','50'])).

thf('52',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','55'])).

thf('57',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    r1_tarski @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['7','17','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('63',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['61','62'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X51 @ X50 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X50 ) @ ( k4_relat_1 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','59'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X42 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('72',plain,(
    ! [X45: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X45 ) )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','75'])).

thf('77',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','59'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

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

thf('80',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('83',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['80'])).

thf('84',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['80'])).

thf('89',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['87','88'])).

thf('90',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['81','89'])).

thf('91',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference(simplify,[status(thm)],['93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZejZoiS6jH
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:18:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.74  % Solved by: fo/fo7.sh
% 0.54/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.74  % done 511 iterations in 0.286s
% 0.54/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.74  % SZS output start Refutation
% 0.54/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.74  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.54/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.74  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.54/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.74  thf(dt_k5_relat_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.54/0.74       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.54/0.74  thf('0', plain,
% 0.54/0.74      (![X43 : $i, X44 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ X43)
% 0.54/0.74          | ~ (v1_relat_1 @ X44)
% 0.54/0.74          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.54/0.74  thf(t60_relat_1, axiom,
% 0.54/0.74    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.54/0.74     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.54/0.74  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.74      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.54/0.74  thf(t37_relat_1, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( v1_relat_1 @ A ) =>
% 0.54/0.74       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.54/0.74         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.54/0.74  thf('2', plain,
% 0.54/0.74      (![X47 : $i]:
% 0.54/0.74         (((k2_relat_1 @ X47) = (k1_relat_1 @ (k4_relat_1 @ X47)))
% 0.54/0.74          | ~ (v1_relat_1 @ X47))),
% 0.54/0.74      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.54/0.74  thf(t21_relat_1, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( v1_relat_1 @ A ) =>
% 0.54/0.74       ( r1_tarski @
% 0.54/0.74         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.54/0.74  thf('3', plain,
% 0.54/0.74      (![X46 : $i]:
% 0.54/0.74         ((r1_tarski @ X46 @ 
% 0.54/0.74           (k2_zfmisc_1 @ (k1_relat_1 @ X46) @ (k2_relat_1 @ X46)))
% 0.54/0.74          | ~ (v1_relat_1 @ X46))),
% 0.54/0.74      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.54/0.74  thf('4', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((r1_tarski @ (k4_relat_1 @ X0) @ 
% 0.54/0.74           (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 0.54/0.74          | ~ (v1_relat_1 @ X0)
% 0.54/0.74          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.74  thf(dt_k4_relat_1, axiom,
% 0.54/0.74    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.54/0.74  thf('5', plain,
% 0.54/0.74      (![X42 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X42)) | ~ (v1_relat_1 @ X42))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.54/0.74  thf('6', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ X0)
% 0.54/0.74          | (r1_tarski @ (k4_relat_1 @ X0) @ 
% 0.54/0.74             (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 0.54/0.74              (k2_relat_1 @ (k4_relat_1 @ X0)))))),
% 0.54/0.74      inference('clc', [status(thm)], ['4', '5'])).
% 0.54/0.74  thf('7', plain,
% 0.54/0.74      (((r1_tarski @ (k4_relat_1 @ k1_xboole_0) @ 
% 0.54/0.74         (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ (k4_relat_1 @ k1_xboole_0))))
% 0.54/0.74        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['1', '6'])).
% 0.54/0.74  thf(t92_xboole_1, axiom,
% 0.54/0.74    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.54/0.74  thf('8', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.54/0.74      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.74  thf(t125_zfmisc_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.54/0.74         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.54/0.74       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.54/0.74         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.54/0.74  thf('9', plain,
% 0.54/0.74      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.54/0.74         ((k2_zfmisc_1 @ (k4_xboole_0 @ X35 @ X37) @ X36)
% 0.54/0.74           = (k4_xboole_0 @ (k2_zfmisc_1 @ X35 @ X36) @ 
% 0.54/0.74              (k2_zfmisc_1 @ X37 @ X36)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.54/0.75  thf(idempotence_k3_xboole_0, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.54/0.75  thf('10', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.54/0.75      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.54/0.75  thf(t100_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.75  thf('11', plain,
% 0.54/0.75      (![X4 : $i, X5 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X4 @ X5)
% 0.54/0.75           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.75  thf('12', plain,
% 0.54/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.75  thf('13', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.54/0.75           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['9', '12'])).
% 0.54/0.75  thf('14', plain,
% 0.54/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.75  thf('15', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.75  thf('16', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.54/0.75  thf('17', plain,
% 0.54/0.75      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['8', '16'])).
% 0.54/0.75  thf(cc1_relat_1, axiom,
% 0.54/0.75    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.54/0.75  thf('18', plain, (![X41 : $i]: ((v1_relat_1 @ X41) | ~ (v1_xboole_0 @ X41))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.54/0.75  thf('19', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.75  thf('20', plain, (![X41 : $i]: ((v1_relat_1 @ X41) | ~ (v1_xboole_0 @ X41))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.54/0.75  thf('21', plain,
% 0.54/0.75      (![X43 : $i, X44 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X43)
% 0.54/0.75          | ~ (v1_relat_1 @ X44)
% 0.54/0.75          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.54/0.75  thf('22', plain, (![X41 : $i]: ((v1_relat_1 @ X41) | ~ (v1_xboole_0 @ X41))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.54/0.75  thf('23', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.54/0.75  thf(t45_relat_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ A ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( v1_relat_1 @ B ) =>
% 0.54/0.75           ( r1_tarski @
% 0.54/0.75             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.54/0.75  thf('24', plain,
% 0.54/0.75      (![X48 : $i, X49 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X48)
% 0.54/0.75          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X49 @ X48)) @ 
% 0.54/0.75             (k2_relat_1 @ X48))
% 0.54/0.75          | ~ (v1_relat_1 @ X49))),
% 0.54/0.75      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.54/0.75  thf('25', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.54/0.75           k1_xboole_0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['23', '24'])).
% 0.54/0.75  thf('26', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.54/0.75             k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['22', '25'])).
% 0.54/0.75  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.54/0.75  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.75      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.75  thf('28', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X0)
% 0.54/0.75          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.54/0.75             k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['26', '27'])).
% 0.54/0.75  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.75  thf('29', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.75  thf(d10_xboole_0, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.75  thf('30', plain,
% 0.54/0.75      (![X1 : $i, X3 : $i]:
% 0.54/0.75         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.75  thf('31', plain,
% 0.54/0.75      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['29', '30'])).
% 0.54/0.75  thf('32', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X0)
% 0.54/0.75          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['28', '31'])).
% 0.54/0.75  thf('33', plain,
% 0.54/0.75      (![X46 : $i]:
% 0.54/0.75         ((r1_tarski @ X46 @ 
% 0.54/0.75           (k2_zfmisc_1 @ (k1_relat_1 @ X46) @ (k2_relat_1 @ X46)))
% 0.54/0.75          | ~ (v1_relat_1 @ X46))),
% 0.54/0.75      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.54/0.75  thf('34', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.54/0.75           (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.54/0.75            k1_xboole_0))
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['32', '33'])).
% 0.54/0.75  thf('35', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.75  thf('36', plain,
% 0.54/0.75      (![X35 : $i, X37 : $i, X38 : $i]:
% 0.54/0.75         ((k2_zfmisc_1 @ X38 @ (k4_xboole_0 @ X35 @ X37))
% 0.54/0.75           = (k4_xboole_0 @ (k2_zfmisc_1 @ X38 @ X35) @ 
% 0.54/0.75              (k2_zfmisc_1 @ X38 @ X37)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.54/0.75  thf('37', plain,
% 0.54/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.75  thf('38', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.54/0.75           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['36', '37'])).
% 0.54/0.75  thf('39', plain,
% 0.54/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.75  thf('40', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.75  thf('41', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.54/0.75  thf('42', plain,
% 0.54/0.75      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['35', '41'])).
% 0.54/0.75  thf('43', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['34', '42'])).
% 0.54/0.75  thf('44', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ k1_xboole_0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['21', '43'])).
% 0.54/0.75  thf('45', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['44'])).
% 0.54/0.75  thf('46', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['20', '45'])).
% 0.54/0.75  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.75      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.75  thf('48', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X0)
% 0.54/0.75          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['46', '47'])).
% 0.54/0.75  thf('49', plain,
% 0.54/0.75      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['29', '30'])).
% 0.54/0.75  thf('50', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X0)
% 0.54/0.75          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['48', '49'])).
% 0.54/0.75  thf('51', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (((k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))
% 0.54/0.75          | ~ (v1_relat_1 @ X1))),
% 0.54/0.75      inference('sup+', [status(thm)], ['19', '50'])).
% 0.54/0.75  thf('52', plain,
% 0.54/0.75      (![X43 : $i, X44 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X43)
% 0.54/0.75          | ~ (v1_relat_1 @ X44)
% 0.54/0.75          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.54/0.75  thf('53', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((v1_relat_1 @ k1_xboole_0)
% 0.54/0.75          | ~ (v1_relat_1 @ X1)
% 0.54/0.75          | ~ (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0))
% 0.54/0.75          | ~ (v1_relat_1 @ X1))),
% 0.54/0.75      inference('sup+', [status(thm)], ['51', '52'])).
% 0.54/0.75  thf('54', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0))
% 0.54/0.75          | ~ (v1_relat_1 @ X1)
% 0.54/0.75          | (v1_relat_1 @ k1_xboole_0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['53'])).
% 0.54/0.75  thf('55', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0)) | (v1_relat_1 @ k1_xboole_0))),
% 0.54/0.75      inference('condensation', [status(thm)], ['54'])).
% 0.54/0.75  thf('56', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))
% 0.54/0.75          | (v1_relat_1 @ k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['18', '55'])).
% 0.54/0.75  thf('57', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.75  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.75      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.75  thf('59', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['57', '58'])).
% 0.54/0.75  thf('60', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.54/0.75      inference('demod', [status(thm)], ['56', '59'])).
% 0.54/0.75  thf('61', plain, ((r1_tarski @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.54/0.75      inference('demod', [status(thm)], ['7', '17', '60'])).
% 0.54/0.75  thf('62', plain,
% 0.54/0.75      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['29', '30'])).
% 0.54/0.75  thf('63', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['61', '62'])).
% 0.54/0.75  thf(t54_relat_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ A ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( v1_relat_1 @ B ) =>
% 0.54/0.75           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.54/0.75             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.54/0.75  thf('64', plain,
% 0.54/0.75      (![X50 : $i, X51 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X50)
% 0.54/0.75          | ((k4_relat_1 @ (k5_relat_1 @ X51 @ X50))
% 0.54/0.75              = (k5_relat_1 @ (k4_relat_1 @ X50) @ (k4_relat_1 @ X51)))
% 0.54/0.75          | ~ (v1_relat_1 @ X51))),
% 0.54/0.75      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.54/0.75  thf('65', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.54/0.75            = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0))
% 0.54/0.75          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['63', '64'])).
% 0.54/0.75  thf('66', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.54/0.75      inference('demod', [status(thm)], ['56', '59'])).
% 0.54/0.75  thf('67', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.54/0.75            = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0))
% 0.54/0.75          | ~ (v1_relat_1 @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['65', '66'])).
% 0.54/0.75  thf('68', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X0)
% 0.54/0.75          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['48', '49'])).
% 0.54/0.75  thf('69', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['67', '68'])).
% 0.54/0.75  thf('70', plain,
% 0.54/0.75      (![X42 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X42)) | ~ (v1_relat_1 @ X42))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.54/0.75  thf('71', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X0)
% 0.54/0.75          | ((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.54/0.75      inference('clc', [status(thm)], ['69', '70'])).
% 0.54/0.75  thf(involutiveness_k4_relat_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.54/0.75  thf('72', plain,
% 0.54/0.75      (![X45 : $i]:
% 0.54/0.75         (((k4_relat_1 @ (k4_relat_1 @ X45)) = (X45)) | ~ (v1_relat_1 @ X45))),
% 0.54/0.75      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.54/0.75  thf('73', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['71', '72'])).
% 0.54/0.75  thf('74', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['61', '62'])).
% 0.54/0.75  thf('75', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['73', '74'])).
% 0.54/0.75  thf('76', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['0', '75'])).
% 0.54/0.75  thf('77', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.54/0.75      inference('demod', [status(thm)], ['56', '59'])).
% 0.54/0.75  thf('78', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['76', '77'])).
% 0.54/0.75  thf('79', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.54/0.75          | ~ (v1_relat_1 @ X0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['78'])).
% 0.54/0.75  thf(t62_relat_1, conjecture,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ A ) =>
% 0.54/0.75       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.54/0.75         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.75    (~( ![A:$i]:
% 0.54/0.75        ( ( v1_relat_1 @ A ) =>
% 0.54/0.75          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.54/0.75            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.54/0.75    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.54/0.75  thf('80', plain,
% 0.54/0.75      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.54/0.75        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('81', plain,
% 0.54/0.75      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.54/0.75         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('split', [status(esa)], ['80'])).
% 0.54/0.75  thf('82', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X0)
% 0.54/0.75          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['48', '49'])).
% 0.54/0.75  thf('83', plain,
% 0.54/0.75      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.54/0.75         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.54/0.75      inference('split', [status(esa)], ['80'])).
% 0.54/0.75  thf('84', plain,
% 0.54/0.75      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.54/0.75         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['82', '83'])).
% 0.54/0.75  thf('85', plain, ((v1_relat_1 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('86', plain,
% 0.54/0.75      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.54/0.75         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['84', '85'])).
% 0.54/0.75  thf('87', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['86'])).
% 0.54/0.75  thf('88', plain,
% 0.54/0.75      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 0.54/0.75       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.54/0.75      inference('split', [status(esa)], ['80'])).
% 0.54/0.75  thf('89', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.54/0.75      inference('sat_resolution*', [status(thm)], ['87', '88'])).
% 0.54/0.75  thf('90', plain, (((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.54/0.75      inference('simpl_trail', [status(thm)], ['81', '89'])).
% 0.54/0.75  thf('91', plain,
% 0.54/0.75      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['79', '90'])).
% 0.54/0.75  thf('92', plain, ((v1_relat_1 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('93', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['91', '92'])).
% 0.54/0.75  thf('94', plain, ($false), inference('simplify', [status(thm)], ['93'])).
% 0.54/0.75  
% 0.54/0.75  % SZS output end Refutation
% 0.54/0.75  
% 0.54/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
