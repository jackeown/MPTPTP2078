%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YgJwbNTrys

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:36 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 589 expanded)
%              Number of leaves         :   36 ( 201 expanded)
%              Depth                    :   29
%              Number of atoms          :  987 (4027 expanded)
%              Number of equality atoms :  109 ( 440 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','4'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('9',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','4'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','4'])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X47 @ X46 ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X47 ) @ ( k4_relat_1 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k6_subset_1 @ X36 @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k6_subset_1 @ X36 @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X47 @ X46 ) )
        = ( k4_xboole_0 @ ( k4_relat_1 @ X47 ) @ ( k4_relat_1 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

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

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('32',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('33',plain,(
    ! [X40: $i] :
      ( ( v1_relat_1 @ X40 )
      | ~ ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    ! [X40: $i] :
      ( ( v1_relat_1 @ X40 )
      | ~ ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('36',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('37',plain,(
    ! [X40: $i] :
      ( ( v1_relat_1 @ X40 )
      | ~ ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('38',plain,
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

thf('39',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X48 @ X49 ) )
        = ( k2_relat_1 @ X49 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) )
      | ~ ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('48',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('50',plain,(
    ! [X45: $i] :
      ( ( ( k3_xboole_0 @ X45 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('52',plain,(
    ! [X45: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) ) )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('55',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('56',plain,(
    ! [X4: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['46','57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['35','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','65'])).

thf('67',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','71'])).

thf('73',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','72'])).

thf('74',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26','73'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('75',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X51 @ X50 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X50 ) @ ( k4_relat_1 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('76',plain,(
    ! [X41: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','65'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','72'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('85',plain,(
    ! [X44: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X44 ) )
        = X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26','73'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','88'])).

thf('90',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','72'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('94',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('98',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('99',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['94'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('104',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['94'])).

thf('107',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['96','107'])).

thf('109',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('112',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    $false ),
    inference(simplify,[status(thm)],['112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YgJwbNTrys
% 0.15/0.37  % Computer   : n012.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 19:48:37 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 1.15/1.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.15/1.39  % Solved by: fo/fo7.sh
% 1.15/1.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.39  % done 1829 iterations in 0.910s
% 1.15/1.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.15/1.39  % SZS output start Refutation
% 1.15/1.39  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.15/1.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.39  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.15/1.39  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.15/1.39  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.15/1.39  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.15/1.39  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.15/1.39  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.15/1.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.39  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.15/1.39  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.15/1.39  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.15/1.39  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.15/1.39  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.15/1.39  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.15/1.39  thf(dt_k5_relat_1, axiom,
% 1.15/1.39    (![A:$i,B:$i]:
% 1.15/1.39     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.15/1.39       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.15/1.39  thf('0', plain,
% 1.15/1.39      (![X42 : $i, X43 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X42)
% 1.15/1.39          | ~ (v1_relat_1 @ X43)
% 1.15/1.39          | (v1_relat_1 @ (k5_relat_1 @ X42 @ X43)))),
% 1.15/1.39      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.15/1.39  thf(t92_xboole_1, axiom,
% 1.15/1.39    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.15/1.39  thf('1', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 1.15/1.39      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.15/1.39  thf(idempotence_k3_xboole_0, axiom,
% 1.15/1.39    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.15/1.39  thf('2', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.15/1.39      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.15/1.39  thf(t100_xboole_1, axiom,
% 1.15/1.39    (![A:$i,B:$i]:
% 1.15/1.39     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.15/1.39  thf('3', plain,
% 1.15/1.39      (![X2 : $i, X3 : $i]:
% 1.15/1.39         ((k4_xboole_0 @ X2 @ X3)
% 1.15/1.39           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.15/1.39      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.39  thf('4', plain,
% 1.15/1.39      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.15/1.39      inference('sup+', [status(thm)], ['2', '3'])).
% 1.15/1.39  thf('5', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 1.15/1.39      inference('demod', [status(thm)], ['1', '4'])).
% 1.15/1.39  thf(l13_xboole_0, axiom,
% 1.15/1.39    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.15/1.39  thf('6', plain,
% 1.15/1.39      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.15/1.39      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.15/1.39  thf('7', plain,
% 1.15/1.39      (![X0 : $i, X1 : $i]:
% 1.15/1.39         (((X1) = (k4_xboole_0 @ X0 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 1.15/1.39      inference('sup+', [status(thm)], ['5', '6'])).
% 1.15/1.39  thf('8', plain,
% 1.15/1.39      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.15/1.39      inference('sup+', [status(thm)], ['2', '3'])).
% 1.15/1.39  thf('9', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 1.15/1.39      inference('demod', [status(thm)], ['1', '4'])).
% 1.15/1.39  thf(t2_boole, axiom,
% 1.15/1.39    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.15/1.39  thf('10', plain,
% 1.15/1.39      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.39      inference('cnf', [status(esa)], [t2_boole])).
% 1.15/1.39  thf('11', plain,
% 1.15/1.39      (![X2 : $i, X3 : $i]:
% 1.15/1.39         ((k4_xboole_0 @ X2 @ X3)
% 1.15/1.39           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.15/1.39      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.39  thf('12', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.15/1.39      inference('sup+', [status(thm)], ['10', '11'])).
% 1.15/1.39  thf('13', plain,
% 1.15/1.39      (![X0 : $i, X1 : $i]:
% 1.15/1.39         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 1.15/1.39           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.15/1.39      inference('sup+', [status(thm)], ['9', '12'])).
% 1.15/1.39  thf('14', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 1.15/1.39           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0)))),
% 1.15/1.39      inference('sup+', [status(thm)], ['8', '13'])).
% 1.15/1.39  thf('15', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 1.15/1.39      inference('demod', [status(thm)], ['1', '4'])).
% 1.15/1.39  thf('16', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.39      inference('demod', [status(thm)], ['14', '15'])).
% 1.15/1.39  thf('17', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (((k4_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 1.15/1.39          | ~ (v1_xboole_0 @ X0))),
% 1.15/1.39      inference('sup+', [status(thm)], ['7', '16'])).
% 1.15/1.39  thf('18', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 1.15/1.39      inference('demod', [status(thm)], ['1', '4'])).
% 1.15/1.39  thf(t41_relat_1, axiom,
% 1.15/1.39    (![A:$i]:
% 1.15/1.39     ( ( v1_relat_1 @ A ) =>
% 1.15/1.39       ( ![B:$i]:
% 1.15/1.39         ( ( v1_relat_1 @ B ) =>
% 1.15/1.39           ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) ) =
% 1.15/1.39             ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) ))).
% 1.15/1.39  thf('19', plain,
% 1.15/1.39      (![X46 : $i, X47 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X46)
% 1.15/1.39          | ((k4_relat_1 @ (k6_subset_1 @ X47 @ X46))
% 1.15/1.39              = (k6_subset_1 @ (k4_relat_1 @ X47) @ (k4_relat_1 @ X46)))
% 1.15/1.39          | ~ (v1_relat_1 @ X47))),
% 1.15/1.39      inference('cnf', [status(esa)], [t41_relat_1])).
% 1.15/1.39  thf(redefinition_k6_subset_1, axiom,
% 1.15/1.39    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.15/1.39  thf('20', plain,
% 1.15/1.39      (![X36 : $i, X37 : $i]:
% 1.15/1.39         ((k6_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))),
% 1.15/1.39      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.15/1.39  thf('21', plain,
% 1.15/1.39      (![X36 : $i, X37 : $i]:
% 1.15/1.39         ((k6_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))),
% 1.15/1.39      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.15/1.39  thf('22', plain,
% 1.15/1.39      (![X46 : $i, X47 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X46)
% 1.15/1.39          | ((k4_relat_1 @ (k4_xboole_0 @ X47 @ X46))
% 1.15/1.39              = (k4_xboole_0 @ (k4_relat_1 @ X47) @ (k4_relat_1 @ X46)))
% 1.15/1.39          | ~ (v1_relat_1 @ X47))),
% 1.15/1.39      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.15/1.39  thf('23', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))
% 1.15/1.39          | ~ (v1_relat_1 @ X0)
% 1.15/1.39          | ~ (v1_relat_1 @ X0))),
% 1.15/1.39      inference('sup+', [status(thm)], ['18', '22'])).
% 1.15/1.39  thf('24', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X0)
% 1.15/1.39          | ((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0)))),
% 1.15/1.39      inference('simplify', [status(thm)], ['23'])).
% 1.15/1.39  thf('25', plain,
% 1.15/1.39      ((((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 1.15/1.39        | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.15/1.39        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.15/1.39      inference('sup+', [status(thm)], ['17', '24'])).
% 1.15/1.39  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.15/1.39  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.39  thf(t62_relat_1, conjecture,
% 1.15/1.39    (![A:$i]:
% 1.15/1.39     ( ( v1_relat_1 @ A ) =>
% 1.15/1.39       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.15/1.39         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 1.15/1.39  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.39    (~( ![A:$i]:
% 1.15/1.39        ( ( v1_relat_1 @ A ) =>
% 1.15/1.39          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.15/1.39            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 1.15/1.39    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 1.15/1.39  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 1.15/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.39  thf('28', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 1.15/1.39      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.15/1.39  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.39  thf('30', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 1.15/1.39      inference('sup+', [status(thm)], ['28', '29'])).
% 1.15/1.39  thf('31', plain,
% 1.15/1.39      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.15/1.39      inference('sup+', [status(thm)], ['2', '3'])).
% 1.15/1.39  thf('32', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 1.15/1.39      inference('demod', [status(thm)], ['30', '31'])).
% 1.15/1.39  thf(cc1_relat_1, axiom,
% 1.15/1.39    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 1.15/1.39  thf('33', plain, (![X40 : $i]: ((v1_relat_1 @ X40) | ~ (v1_xboole_0 @ X40))),
% 1.15/1.39      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.15/1.39  thf('34', plain,
% 1.15/1.39      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.15/1.39      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.15/1.39  thf('35', plain, (![X40 : $i]: ((v1_relat_1 @ X40) | ~ (v1_xboole_0 @ X40))),
% 1.15/1.39      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.15/1.39  thf('36', plain,
% 1.15/1.39      (![X42 : $i, X43 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X42)
% 1.15/1.39          | ~ (v1_relat_1 @ X43)
% 1.15/1.39          | (v1_relat_1 @ (k5_relat_1 @ X42 @ X43)))),
% 1.15/1.39      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.15/1.39  thf('37', plain, (![X40 : $i]: ((v1_relat_1 @ X40) | ~ (v1_xboole_0 @ X40))),
% 1.15/1.39      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.15/1.39  thf(t60_relat_1, axiom,
% 1.15/1.39    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.15/1.39     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.15/1.39  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.39      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.15/1.39  thf(t47_relat_1, axiom,
% 1.15/1.39    (![A:$i]:
% 1.15/1.39     ( ( v1_relat_1 @ A ) =>
% 1.15/1.39       ( ![B:$i]:
% 1.15/1.39         ( ( v1_relat_1 @ B ) =>
% 1.15/1.39           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 1.15/1.39             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.15/1.39  thf('39', plain,
% 1.15/1.39      (![X48 : $i, X49 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X48)
% 1.15/1.39          | ((k2_relat_1 @ (k5_relat_1 @ X48 @ X49)) = (k2_relat_1 @ X49))
% 1.15/1.39          | ~ (r1_tarski @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X48))
% 1.15/1.39          | ~ (v1_relat_1 @ X49))),
% 1.15/1.39      inference('cnf', [status(esa)], [t47_relat_1])).
% 1.15/1.39  thf('40', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 1.15/1.39          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.15/1.39          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.15/1.39              = (k2_relat_1 @ k1_xboole_0))
% 1.15/1.39          | ~ (v1_relat_1 @ X0))),
% 1.15/1.39      inference('sup-', [status(thm)], ['38', '39'])).
% 1.15/1.39  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.15/1.39  thf('41', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.15/1.39      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.15/1.39  thf('42', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.39      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.15/1.39  thf('43', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ k1_xboole_0)
% 1.15/1.39          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 1.15/1.39          | ~ (v1_relat_1 @ X0))),
% 1.15/1.39      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.15/1.39  thf('44', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.15/1.39          | ~ (v1_relat_1 @ X0)
% 1.15/1.39          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 1.15/1.39      inference('sup-', [status(thm)], ['37', '43'])).
% 1.15/1.39  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.39  thf('46', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X0)
% 1.15/1.39          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 1.15/1.39      inference('demod', [status(thm)], ['44', '45'])).
% 1.15/1.39  thf(fc3_zfmisc_1, axiom,
% 1.15/1.39    (![A:$i,B:$i]:
% 1.15/1.39     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 1.15/1.39  thf('47', plain,
% 1.15/1.39      (![X34 : $i, X35 : $i]:
% 1.15/1.39         ((v1_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35)) | ~ (v1_xboole_0 @ X35))),
% 1.15/1.39      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 1.15/1.39  thf('48', plain,
% 1.15/1.39      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.15/1.39      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.15/1.39  thf('49', plain,
% 1.15/1.39      (![X0 : $i, X1 : $i]:
% 1.15/1.39         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.15/1.39      inference('sup-', [status(thm)], ['47', '48'])).
% 1.15/1.39  thf(t22_relat_1, axiom,
% 1.15/1.39    (![A:$i]:
% 1.15/1.39     ( ( v1_relat_1 @ A ) =>
% 1.15/1.39       ( ( k3_xboole_0 @
% 1.15/1.39           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 1.15/1.39         ( A ) ) ))).
% 1.15/1.39  thf('50', plain,
% 1.15/1.39      (![X45 : $i]:
% 1.15/1.39         (((k3_xboole_0 @ X45 @ 
% 1.15/1.39            (k2_zfmisc_1 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))) = (
% 1.15/1.39            X45))
% 1.15/1.39          | ~ (v1_relat_1 @ X45))),
% 1.15/1.39      inference('cnf', [status(esa)], [t22_relat_1])).
% 1.15/1.39  thf(t12_setfam_1, axiom,
% 1.15/1.39    (![A:$i,B:$i]:
% 1.15/1.39     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.15/1.39  thf('51', plain,
% 1.15/1.39      (![X38 : $i, X39 : $i]:
% 1.15/1.39         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 1.15/1.39      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.15/1.39  thf('52', plain,
% 1.15/1.39      (![X45 : $i]:
% 1.15/1.39         (((k1_setfam_1 @ 
% 1.15/1.39            (k2_tarski @ X45 @ 
% 1.15/1.39             (k2_zfmisc_1 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))))
% 1.15/1.39            = (X45))
% 1.15/1.39          | ~ (v1_relat_1 @ X45))),
% 1.15/1.39      inference('demod', [status(thm)], ['50', '51'])).
% 1.15/1.39  thf('53', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (X0))
% 1.15/1.39          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 1.15/1.39          | ~ (v1_relat_1 @ X0))),
% 1.15/1.39      inference('sup+', [status(thm)], ['49', '52'])).
% 1.15/1.39  thf('54', plain,
% 1.15/1.39      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.39      inference('cnf', [status(esa)], [t2_boole])).
% 1.15/1.39  thf('55', plain,
% 1.15/1.39      (![X38 : $i, X39 : $i]:
% 1.15/1.39         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 1.15/1.39      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.15/1.39  thf('56', plain,
% 1.15/1.39      (![X4 : $i]:
% 1.15/1.39         ((k1_setfam_1 @ (k2_tarski @ X4 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.15/1.39      inference('demod', [status(thm)], ['54', '55'])).
% 1.15/1.39  thf('57', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (((k1_xboole_0) = (X0))
% 1.15/1.39          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 1.15/1.39          | ~ (v1_relat_1 @ X0))),
% 1.15/1.39      inference('demod', [status(thm)], ['53', '56'])).
% 1.15/1.39  thf('58', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.15/1.39          | ~ (v1_relat_1 @ X0)
% 1.15/1.39          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.15/1.39          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.15/1.39      inference('sup-', [status(thm)], ['46', '57'])).
% 1.15/1.39  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.39  thf('60', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X0)
% 1.15/1.39          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.15/1.39          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.15/1.39      inference('demod', [status(thm)], ['58', '59'])).
% 1.15/1.39  thf('61', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ k1_xboole_0)
% 1.15/1.39          | ~ (v1_relat_1 @ X0)
% 1.15/1.39          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.15/1.39          | ~ (v1_relat_1 @ X0))),
% 1.15/1.39      inference('sup-', [status(thm)], ['36', '60'])).
% 1.15/1.39  thf('62', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.15/1.39          | ~ (v1_relat_1 @ X0)
% 1.15/1.39          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.15/1.39      inference('simplify', [status(thm)], ['61'])).
% 1.15/1.39  thf('63', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.15/1.39          | ~ (v1_relat_1 @ X0)
% 1.15/1.39          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.15/1.39      inference('sup-', [status(thm)], ['35', '62'])).
% 1.15/1.39  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.39  thf('65', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X0)
% 1.15/1.39          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.15/1.39      inference('demod', [status(thm)], ['63', '64'])).
% 1.15/1.39  thf('66', plain,
% 1.15/1.39      (![X0 : $i, X1 : $i]:
% 1.15/1.39         (((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 1.15/1.39          | ~ (v1_xboole_0 @ X0)
% 1.15/1.39          | ~ (v1_relat_1 @ X1))),
% 1.15/1.39      inference('sup+', [status(thm)], ['34', '65'])).
% 1.15/1.39  thf('67', plain,
% 1.15/1.39      (![X42 : $i, X43 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X42)
% 1.15/1.39          | ~ (v1_relat_1 @ X43)
% 1.15/1.39          | (v1_relat_1 @ (k5_relat_1 @ X42 @ X43)))),
% 1.15/1.39      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.15/1.39  thf('68', plain,
% 1.15/1.39      (![X0 : $i, X1 : $i]:
% 1.15/1.39         ((v1_relat_1 @ k1_xboole_0)
% 1.15/1.39          | ~ (v1_relat_1 @ X1)
% 1.15/1.39          | ~ (v1_xboole_0 @ X0)
% 1.15/1.39          | ~ (v1_relat_1 @ X0)
% 1.15/1.39          | ~ (v1_relat_1 @ X1))),
% 1.15/1.39      inference('sup+', [status(thm)], ['66', '67'])).
% 1.15/1.39  thf('69', plain,
% 1.15/1.39      (![X0 : $i, X1 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X0)
% 1.15/1.39          | ~ (v1_xboole_0 @ X0)
% 1.15/1.39          | ~ (v1_relat_1 @ X1)
% 1.15/1.39          | (v1_relat_1 @ k1_xboole_0))),
% 1.15/1.39      inference('simplify', [status(thm)], ['68'])).
% 1.15/1.39  thf('70', plain,
% 1.15/1.39      (![X0 : $i, X1 : $i]:
% 1.15/1.39         (~ (v1_xboole_0 @ X0)
% 1.15/1.39          | (v1_relat_1 @ k1_xboole_0)
% 1.15/1.39          | ~ (v1_relat_1 @ X1)
% 1.15/1.39          | ~ (v1_xboole_0 @ X0))),
% 1.15/1.39      inference('sup-', [status(thm)], ['33', '69'])).
% 1.15/1.39  thf('71', plain,
% 1.15/1.39      (![X0 : $i, X1 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X1)
% 1.15/1.39          | (v1_relat_1 @ k1_xboole_0)
% 1.15/1.39          | ~ (v1_xboole_0 @ X0))),
% 1.15/1.39      inference('simplify', [status(thm)], ['70'])).
% 1.15/1.39  thf('72', plain,
% 1.15/1.39      (![X1 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X1))),
% 1.15/1.39      inference('sup-', [status(thm)], ['32', '71'])).
% 1.15/1.39  thf('73', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.15/1.39      inference('sup-', [status(thm)], ['27', '72'])).
% 1.15/1.39  thf('74', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.39      inference('demod', [status(thm)], ['25', '26', '73'])).
% 1.15/1.39  thf(t54_relat_1, axiom,
% 1.15/1.39    (![A:$i]:
% 1.15/1.39     ( ( v1_relat_1 @ A ) =>
% 1.15/1.39       ( ![B:$i]:
% 1.15/1.39         ( ( v1_relat_1 @ B ) =>
% 1.15/1.39           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.15/1.39             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 1.15/1.39  thf('75', plain,
% 1.15/1.39      (![X50 : $i, X51 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X50)
% 1.15/1.39          | ((k4_relat_1 @ (k5_relat_1 @ X51 @ X50))
% 1.15/1.39              = (k5_relat_1 @ (k4_relat_1 @ X50) @ (k4_relat_1 @ X51)))
% 1.15/1.39          | ~ (v1_relat_1 @ X51))),
% 1.15/1.39      inference('cnf', [status(esa)], [t54_relat_1])).
% 1.15/1.39  thf(dt_k4_relat_1, axiom,
% 1.15/1.39    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 1.15/1.39  thf('76', plain,
% 1.15/1.39      (![X41 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X41)) | ~ (v1_relat_1 @ X41))),
% 1.15/1.39      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.15/1.39  thf('77', plain,
% 1.15/1.39      (![X0 : $i, X1 : $i]:
% 1.15/1.39         (((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 1.15/1.39          | ~ (v1_xboole_0 @ X0)
% 1.15/1.39          | ~ (v1_relat_1 @ X1))),
% 1.15/1.39      inference('sup+', [status(thm)], ['34', '65'])).
% 1.15/1.39  thf('78', plain,
% 1.15/1.39      (![X0 : $i, X1 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X0)
% 1.15/1.39          | ~ (v1_xboole_0 @ X1)
% 1.15/1.39          | ((k1_xboole_0) = (k5_relat_1 @ (k4_relat_1 @ X0) @ X1)))),
% 1.15/1.39      inference('sup-', [status(thm)], ['76', '77'])).
% 1.15/1.39  thf('79', plain,
% 1.15/1.39      (![X0 : $i, X1 : $i]:
% 1.15/1.39         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.15/1.39          | ~ (v1_relat_1 @ X1)
% 1.15/1.39          | ~ (v1_relat_1 @ X0)
% 1.15/1.39          | ~ (v1_xboole_0 @ (k4_relat_1 @ X1))
% 1.15/1.39          | ~ (v1_relat_1 @ X0))),
% 1.15/1.39      inference('sup+', [status(thm)], ['75', '78'])).
% 1.15/1.39  thf('80', plain,
% 1.15/1.39      (![X0 : $i, X1 : $i]:
% 1.15/1.39         (~ (v1_xboole_0 @ (k4_relat_1 @ X1))
% 1.15/1.39          | ~ (v1_relat_1 @ X0)
% 1.15/1.39          | ~ (v1_relat_1 @ X1)
% 1.15/1.39          | ((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 1.15/1.39      inference('simplify', [status(thm)], ['79'])).
% 1.15/1.39  thf('81', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.15/1.39          | ((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 1.15/1.39          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.15/1.39          | ~ (v1_relat_1 @ X0))),
% 1.15/1.39      inference('sup-', [status(thm)], ['74', '80'])).
% 1.15/1.39  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.39  thf('83', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.15/1.39      inference('sup-', [status(thm)], ['27', '72'])).
% 1.15/1.39  thf('84', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 1.15/1.39          | ~ (v1_relat_1 @ X0))),
% 1.15/1.39      inference('demod', [status(thm)], ['81', '82', '83'])).
% 1.15/1.39  thf(involutiveness_k4_relat_1, axiom,
% 1.15/1.39    (![A:$i]:
% 1.15/1.39     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 1.15/1.39  thf('85', plain,
% 1.15/1.39      (![X44 : $i]:
% 1.15/1.39         (((k4_relat_1 @ (k4_relat_1 @ X44)) = (X44)) | ~ (v1_relat_1 @ X44))),
% 1.15/1.39      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 1.15/1.39  thf('86', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.15/1.39          | ~ (v1_relat_1 @ X0)
% 1.15/1.39          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.15/1.39      inference('sup+', [status(thm)], ['84', '85'])).
% 1.15/1.39  thf('87', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.39      inference('demod', [status(thm)], ['25', '26', '73'])).
% 1.15/1.39  thf('88', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.15/1.39          | ~ (v1_relat_1 @ X0)
% 1.15/1.39          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.15/1.39      inference('demod', [status(thm)], ['86', '87'])).
% 1.15/1.39  thf('89', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X0)
% 1.15/1.39          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.15/1.39          | ~ (v1_relat_1 @ X0)
% 1.15/1.39          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.15/1.39      inference('sup-', [status(thm)], ['0', '88'])).
% 1.15/1.39  thf('90', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.15/1.39      inference('sup-', [status(thm)], ['27', '72'])).
% 1.15/1.39  thf('91', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X0)
% 1.15/1.39          | ~ (v1_relat_1 @ X0)
% 1.15/1.39          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.15/1.39      inference('demod', [status(thm)], ['89', '90'])).
% 1.15/1.39  thf('92', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.15/1.39          | ~ (v1_relat_1 @ X0))),
% 1.15/1.39      inference('simplify', [status(thm)], ['91'])).
% 1.15/1.39  thf('93', plain,
% 1.15/1.39      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.15/1.39      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.15/1.39  thf('94', plain,
% 1.15/1.39      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 1.15/1.39        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 1.15/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.39  thf('95', plain,
% 1.15/1.39      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 1.15/1.39         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.15/1.39      inference('split', [status(esa)], ['94'])).
% 1.15/1.39  thf('96', plain,
% 1.15/1.39      ((![X0 : $i]:
% 1.15/1.39          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.15/1.39         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.15/1.39      inference('sup-', [status(thm)], ['93', '95'])).
% 1.15/1.39  thf('97', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (~ (v1_relat_1 @ X0)
% 1.15/1.39          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.15/1.39      inference('demod', [status(thm)], ['63', '64'])).
% 1.15/1.39  thf('98', plain,
% 1.15/1.39      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.15/1.39      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.15/1.39  thf('99', plain,
% 1.15/1.39      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 1.15/1.39         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.15/1.39      inference('split', [status(esa)], ['94'])).
% 1.15/1.39  thf('100', plain,
% 1.15/1.39      ((![X0 : $i]:
% 1.15/1.39          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.15/1.39         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.15/1.39      inference('sup-', [status(thm)], ['98', '99'])).
% 1.15/1.39  thf('101', plain,
% 1.15/1.39      (((((k1_xboole_0) != (k1_xboole_0))
% 1.15/1.39         | ~ (v1_relat_1 @ sk_A)
% 1.15/1.39         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.15/1.39         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.15/1.39      inference('sup-', [status(thm)], ['97', '100'])).
% 1.15/1.39  thf('102', plain, ((v1_relat_1 @ sk_A)),
% 1.15/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.39  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.39  thf('104', plain,
% 1.15/1.39      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.15/1.39         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.15/1.39      inference('demod', [status(thm)], ['101', '102', '103'])).
% 1.15/1.39  thf('105', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 1.15/1.39      inference('simplify', [status(thm)], ['104'])).
% 1.15/1.39  thf('106', plain,
% 1.15/1.39      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 1.15/1.39       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 1.15/1.39      inference('split', [status(esa)], ['94'])).
% 1.15/1.39  thf('107', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.15/1.39      inference('sat_resolution*', [status(thm)], ['105', '106'])).
% 1.15/1.39  thf('108', plain,
% 1.15/1.39      (![X0 : $i]:
% 1.15/1.39         (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.15/1.39      inference('simpl_trail', [status(thm)], ['96', '107'])).
% 1.15/1.39  thf('109', plain,
% 1.15/1.39      ((((k1_xboole_0) != (k1_xboole_0))
% 1.15/1.39        | ~ (v1_relat_1 @ sk_A)
% 1.15/1.39        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.15/1.39      inference('sup-', [status(thm)], ['92', '108'])).
% 1.15/1.39  thf('110', plain, ((v1_relat_1 @ sk_A)),
% 1.15/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.39  thf('111', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.39  thf('112', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.15/1.39      inference('demod', [status(thm)], ['109', '110', '111'])).
% 1.15/1.39  thf('113', plain, ($false), inference('simplify', [status(thm)], ['112'])).
% 1.15/1.39  
% 1.15/1.39  % SZS output end Refutation
% 1.15/1.39  
% 1.22/1.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
