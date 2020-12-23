%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nqKCsUYzW5

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:27 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  181 (2723 expanded)
%              Number of leaves         :   28 ( 908 expanded)
%              Depth                    :   51
%              Number of atoms          : 1231 (18138 expanded)
%              Number of equality atoms :  114 (1747 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('2',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
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

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X32: $i] :
      ( ( ( k1_relat_1 @ X32 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) )
      | ~ ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('8',plain,(
    ! [X31: $i] :
      ( ( ( k3_xboole_0 @ X31 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

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
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('15',plain,
    ( ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X36 @ X35 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X35 ) @ ( k4_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('28',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('29',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('30',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X34 @ X33 ) ) @ ( k1_relat_1 @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('34',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('36',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('42',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('43',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('44',plain,(
    ! [X32: $i] :
      ( ( ( k2_relat_1 @ X32 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('45',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X31: $i] :
      ( ( ( k3_xboole_0 @ X31 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('60',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('62',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_xboole_0
      = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['58','71'])).

thf('73',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('74',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('75',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X34 @ X33 ) ) @ ( k1_relat_1 @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('76',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('78',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['80','81'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('83',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('84',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,
    ( k1_xboole_0
    = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('91',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('95',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['93','100'])).

thf('102',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['89','101'])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('104',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('105',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','112'])).

thf('114',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','118'])).

thf('120',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('123',plain,(
    ! [X30: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X30 ) )
        = X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','126'])).

thf('128',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
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

thf('132',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['132'])).

thf('134',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('137',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['132'])).

thf('138',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('142',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['132'])).

thf('145',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['134','145'])).

thf('147',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['130','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('150',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    $false ),
    inference(simplify,[status(thm)],['150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nqKCsUYzW5
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:48:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.61/1.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.61/1.80  % Solved by: fo/fo7.sh
% 1.61/1.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.61/1.80  % done 2127 iterations in 1.339s
% 1.61/1.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.61/1.80  % SZS output start Refutation
% 1.61/1.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.61/1.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.61/1.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.61/1.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.61/1.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.61/1.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.61/1.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.61/1.80  thf(sk_A_type, type, sk_A: $i).
% 1.61/1.80  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.61/1.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.61/1.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.61/1.80  thf(dt_k5_relat_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.61/1.80       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.61/1.80  thf('0', plain,
% 1.61/1.80      (![X28 : $i, X29 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X28)
% 1.61/1.80          | ~ (v1_relat_1 @ X29)
% 1.61/1.80          | (v1_relat_1 @ (k5_relat_1 @ X28 @ X29)))),
% 1.61/1.80      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.61/1.80  thf(cc1_relat_1, axiom,
% 1.61/1.80    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 1.61/1.80  thf('1', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 1.61/1.80      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.61/1.80  thf('2', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 1.61/1.80      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.61/1.80  thf(t60_relat_1, axiom,
% 1.61/1.80    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.61/1.80     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.61/1.80  thf('3', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.80      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.61/1.80  thf(t37_relat_1, axiom,
% 1.61/1.80    (![A:$i]:
% 1.61/1.80     ( ( v1_relat_1 @ A ) =>
% 1.61/1.80       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.61/1.80         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.61/1.80  thf('4', plain,
% 1.61/1.80      (![X32 : $i]:
% 1.61/1.80         (((k1_relat_1 @ X32) = (k2_relat_1 @ (k4_relat_1 @ X32)))
% 1.61/1.80          | ~ (v1_relat_1 @ X32))),
% 1.61/1.80      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.61/1.80  thf(fc3_zfmisc_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 1.61/1.80  thf('5', plain,
% 1.61/1.80      (![X20 : $i, X21 : $i]:
% 1.61/1.80         ((v1_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21)) | ~ (v1_xboole_0 @ X21))),
% 1.61/1.80      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 1.61/1.80  thf(l13_xboole_0, axiom,
% 1.61/1.80    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.61/1.80  thf('6', plain,
% 1.61/1.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.61/1.80  thf('7', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['5', '6'])).
% 1.61/1.80  thf(t22_relat_1, axiom,
% 1.61/1.80    (![A:$i]:
% 1.61/1.80     ( ( v1_relat_1 @ A ) =>
% 1.61/1.80       ( ( k3_xboole_0 @
% 1.61/1.80           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 1.61/1.80         ( A ) ) ))).
% 1.61/1.80  thf('8', plain,
% 1.61/1.80      (![X31 : $i]:
% 1.61/1.80         (((k3_xboole_0 @ X31 @ 
% 1.61/1.80            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))) = (
% 1.61/1.80            X31))
% 1.61/1.80          | ~ (v1_relat_1 @ X31))),
% 1.61/1.80      inference('cnf', [status(esa)], [t22_relat_1])).
% 1.61/1.80  thf('9', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 1.61/1.80          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['7', '8'])).
% 1.61/1.80  thf(t2_boole, axiom,
% 1.61/1.80    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.61/1.80  thf('10', plain,
% 1.61/1.80      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.80      inference('cnf', [status(esa)], [t2_boole])).
% 1.61/1.80  thf('11', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k1_xboole_0) = (X0))
% 1.61/1.80          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('demod', [status(thm)], ['9', '10'])).
% 1.61/1.80  thf('12', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.61/1.80          | ~ (v1_relat_1 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 1.61/1.80          | ((k1_xboole_0) = (k4_relat_1 @ X0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['4', '11'])).
% 1.61/1.80  thf('13', plain,
% 1.61/1.80      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.61/1.80        | ((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 1.61/1.80        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 1.61/1.80        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['3', '12'])).
% 1.61/1.80  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.61/1.80  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.80  thf('15', plain,
% 1.61/1.80      ((((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 1.61/1.80        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 1.61/1.80        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['13', '14'])).
% 1.61/1.80  thf(dt_k4_relat_1, axiom,
% 1.61/1.80    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 1.61/1.80  thf('16', plain,
% 1.61/1.80      (![X27 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X27)) | ~ (v1_relat_1 @ X27))),
% 1.61/1.80      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.61/1.80  thf('17', plain,
% 1.61/1.80      ((~ (v1_relat_1 @ k1_xboole_0)
% 1.61/1.80        | ((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0)))),
% 1.61/1.80      inference('clc', [status(thm)], ['15', '16'])).
% 1.61/1.80  thf('18', plain,
% 1.61/1.80      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.61/1.80        | ((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['2', '17'])).
% 1.61/1.80  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.80  thf('20', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['18', '19'])).
% 1.61/1.80  thf(t54_relat_1, axiom,
% 1.61/1.80    (![A:$i]:
% 1.61/1.80     ( ( v1_relat_1 @ A ) =>
% 1.61/1.80       ( ![B:$i]:
% 1.61/1.80         ( ( v1_relat_1 @ B ) =>
% 1.61/1.80           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.61/1.80             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 1.61/1.80  thf('21', plain,
% 1.61/1.80      (![X35 : $i, X36 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X35)
% 1.61/1.80          | ((k4_relat_1 @ (k5_relat_1 @ X36 @ X35))
% 1.61/1.80              = (k5_relat_1 @ (k4_relat_1 @ X35) @ (k4_relat_1 @ X36)))
% 1.61/1.80          | ~ (v1_relat_1 @ X36))),
% 1.61/1.80      inference('cnf', [status(esa)], [t54_relat_1])).
% 1.61/1.80  thf('22', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.61/1.80            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 1.61/1.80          | ~ (v1_relat_1 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['20', '21'])).
% 1.61/1.80  thf('23', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.61/1.80          | ~ (v1_relat_1 @ X0)
% 1.61/1.80          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.61/1.80              = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0))))),
% 1.61/1.80      inference('sup-', [status(thm)], ['1', '22'])).
% 1.61/1.80  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.80  thf('25', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X0)
% 1.61/1.80          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.61/1.80              = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0))))),
% 1.61/1.80      inference('demod', [status(thm)], ['23', '24'])).
% 1.61/1.80  thf('26', plain,
% 1.61/1.80      (![X27 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X27)) | ~ (v1_relat_1 @ X27))),
% 1.61/1.80      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.61/1.80  thf('27', plain,
% 1.61/1.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.61/1.80  thf('28', plain,
% 1.61/1.80      (![X28 : $i, X29 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X28)
% 1.61/1.80          | ~ (v1_relat_1 @ X29)
% 1.61/1.80          | (v1_relat_1 @ (k5_relat_1 @ X28 @ X29)))),
% 1.61/1.80      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.61/1.80  thf('29', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.80      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.61/1.80  thf(t44_relat_1, axiom,
% 1.61/1.80    (![A:$i]:
% 1.61/1.80     ( ( v1_relat_1 @ A ) =>
% 1.61/1.80       ( ![B:$i]:
% 1.61/1.80         ( ( v1_relat_1 @ B ) =>
% 1.61/1.80           ( r1_tarski @
% 1.61/1.80             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 1.61/1.80  thf('30', plain,
% 1.61/1.80      (![X33 : $i, X34 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X33)
% 1.61/1.80          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X34 @ X33)) @ 
% 1.61/1.80             (k1_relat_1 @ X34))
% 1.61/1.80          | ~ (v1_relat_1 @ X34))),
% 1.61/1.80      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.61/1.80  thf('31', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.61/1.80           k1_xboole_0)
% 1.61/1.80          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['29', '30'])).
% 1.61/1.80  thf('32', plain,
% 1.61/1.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.61/1.80  thf('33', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 1.61/1.80      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.61/1.80  thf('34', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['18', '19'])).
% 1.61/1.80  thf('35', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X0)
% 1.61/1.80          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.61/1.80              = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0))))),
% 1.61/1.80      inference('demod', [status(thm)], ['23', '24'])).
% 1.61/1.80  thf('36', plain,
% 1.61/1.80      ((((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80          = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['34', '35'])).
% 1.61/1.80  thf('37', plain,
% 1.61/1.80      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.61/1.80        | ((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80            = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['33', '36'])).
% 1.61/1.80  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.80  thf('39', plain,
% 1.61/1.80      (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80         = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['37', '38'])).
% 1.61/1.80  thf('40', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.61/1.80            = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80          | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['32', '39'])).
% 1.61/1.80  thf('41', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 1.61/1.80      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.61/1.80  thf('42', plain,
% 1.61/1.80      (![X28 : $i, X29 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X28)
% 1.61/1.80          | ~ (v1_relat_1 @ X29)
% 1.61/1.80          | (v1_relat_1 @ (k5_relat_1 @ X28 @ X29)))),
% 1.61/1.80      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.61/1.80  thf('43', plain,
% 1.61/1.80      (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80         = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['37', '38'])).
% 1.61/1.80  thf('44', plain,
% 1.61/1.80      (![X32 : $i]:
% 1.61/1.80         (((k2_relat_1 @ X32) = (k1_relat_1 @ (k4_relat_1 @ X32)))
% 1.61/1.80          | ~ (v1_relat_1 @ X32))),
% 1.61/1.80      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.61/1.80  thf('45', plain,
% 1.61/1.80      ((((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80          = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))
% 1.61/1.80        | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.61/1.80      inference('sup+', [status(thm)], ['43', '44'])).
% 1.61/1.80  thf('46', plain,
% 1.61/1.80      ((~ (v1_relat_1 @ k1_xboole_0)
% 1.61/1.80        | ~ (v1_relat_1 @ k1_xboole_0)
% 1.61/1.80        | ((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80            = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))))),
% 1.61/1.80      inference('sup-', [status(thm)], ['42', '45'])).
% 1.61/1.80  thf('47', plain,
% 1.61/1.80      ((((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80          = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))
% 1.61/1.80        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.61/1.80      inference('simplify', [status(thm)], ['46'])).
% 1.61/1.80  thf('48', plain,
% 1.61/1.80      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.61/1.80        | ((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80            = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))))),
% 1.61/1.80      inference('sup-', [status(thm)], ['41', '47'])).
% 1.61/1.80  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.80  thf('50', plain,
% 1.61/1.80      (((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80         = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.61/1.80      inference('demod', [status(thm)], ['48', '49'])).
% 1.61/1.80  thf(fc4_zfmisc_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 1.61/1.80  thf('51', plain,
% 1.61/1.80      (![X22 : $i, X23 : $i]:
% 1.61/1.80         (~ (v1_xboole_0 @ X22) | (v1_xboole_0 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 1.61/1.80      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 1.61/1.80  thf('52', plain,
% 1.61/1.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.61/1.80  thf('53', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['51', '52'])).
% 1.61/1.80  thf('54', plain,
% 1.61/1.80      (![X31 : $i]:
% 1.61/1.80         (((k3_xboole_0 @ X31 @ 
% 1.61/1.80            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))) = (
% 1.61/1.80            X31))
% 1.61/1.80          | ~ (v1_relat_1 @ X31))),
% 1.61/1.80      inference('cnf', [status(esa)], [t22_relat_1])).
% 1.61/1.80  thf('55', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 1.61/1.80          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['53', '54'])).
% 1.61/1.80  thf('56', plain,
% 1.61/1.80      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.80      inference('cnf', [status(esa)], [t2_boole])).
% 1.61/1.80  thf('57', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k1_xboole_0) = (X0))
% 1.61/1.80          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('demod', [status(thm)], ['55', '56'])).
% 1.61/1.80  thf('58', plain,
% 1.61/1.80      ((~ (v1_xboole_0 @ 
% 1.61/1.80           (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))
% 1.61/1.80        | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80        | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['50', '57'])).
% 1.61/1.80  thf('59', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 1.61/1.80      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.61/1.80  thf('60', plain,
% 1.61/1.80      (![X28 : $i, X29 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X28)
% 1.61/1.80          | ~ (v1_relat_1 @ X29)
% 1.61/1.80          | (v1_relat_1 @ (k5_relat_1 @ X28 @ X29)))),
% 1.61/1.80      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.61/1.80  thf('61', plain,
% 1.61/1.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.61/1.80  thf('62', plain,
% 1.61/1.80      (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80         = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['37', '38'])).
% 1.61/1.80  thf('63', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.61/1.80            = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80          | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['61', '62'])).
% 1.61/1.80  thf('64', plain,
% 1.61/1.80      (![X27 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X27)) | ~ (v1_relat_1 @ X27))),
% 1.61/1.80      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.61/1.80  thf('65', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         ((v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80          | ~ (v1_xboole_0 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.61/1.80      inference('sup+', [status(thm)], ['63', '64'])).
% 1.61/1.80  thf('66', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ k1_xboole_0)
% 1.61/1.80          | ~ (v1_relat_1 @ X0)
% 1.61/1.80          | ~ (v1_xboole_0 @ X0)
% 1.61/1.80          | (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['60', '65'])).
% 1.61/1.80  thf('67', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.61/1.80          | (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80          | ~ (v1_xboole_0 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['59', '66'])).
% 1.61/1.80  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.80  thf('69', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         ((v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80          | ~ (v1_xboole_0 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('demod', [status(thm)], ['67', '68'])).
% 1.61/1.80  thf('70', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 1.61/1.80      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.61/1.80  thf('71', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_xboole_0 @ X0)
% 1.61/1.80          | (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.61/1.80      inference('clc', [status(thm)], ['69', '70'])).
% 1.61/1.80  thf('72', plain,
% 1.61/1.80      ((((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80        | ~ (v1_xboole_0 @ 
% 1.61/1.80             (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))))),
% 1.61/1.80      inference('clc', [status(thm)], ['58', '71'])).
% 1.61/1.80  thf('73', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 1.61/1.80      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.61/1.80  thf('74', plain,
% 1.61/1.80      (((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80         = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.61/1.80      inference('demod', [status(thm)], ['48', '49'])).
% 1.61/1.80  thf('75', plain,
% 1.61/1.80      (![X33 : $i, X34 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X33)
% 1.61/1.80          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X34 @ X33)) @ 
% 1.61/1.80             (k1_relat_1 @ X34))
% 1.61/1.80          | ~ (v1_relat_1 @ X34))),
% 1.61/1.80      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.61/1.80  thf('76', plain,
% 1.61/1.80      (((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)) @ 
% 1.61/1.80         (k1_relat_1 @ k1_xboole_0))
% 1.61/1.80        | ~ (v1_relat_1 @ k1_xboole_0)
% 1.61/1.80        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['74', '75'])).
% 1.61/1.80  thf('77', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.80      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.61/1.80  thf('78', plain,
% 1.61/1.80      (((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)) @ 
% 1.61/1.80         k1_xboole_0)
% 1.61/1.80        | ~ (v1_relat_1 @ k1_xboole_0)
% 1.61/1.80        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['76', '77'])).
% 1.61/1.80  thf('79', plain,
% 1.61/1.80      ((~ (v1_relat_1 @ k1_xboole_0)
% 1.61/1.80        | (r1_tarski @ 
% 1.61/1.80           (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)) @ 
% 1.61/1.80           k1_xboole_0))),
% 1.61/1.80      inference('simplify', [status(thm)], ['78'])).
% 1.61/1.80  thf('80', plain,
% 1.61/1.80      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.61/1.80        | (r1_tarski @ 
% 1.61/1.80           (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)) @ 
% 1.61/1.80           k1_xboole_0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['73', '79'])).
% 1.61/1.80  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.80  thf('82', plain,
% 1.61/1.80      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)) @ 
% 1.61/1.80        k1_xboole_0)),
% 1.61/1.80      inference('demod', [status(thm)], ['80', '81'])).
% 1.61/1.80  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.61/1.80  thf('83', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.61/1.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.61/1.80  thf(d10_xboole_0, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.61/1.80  thf('84', plain,
% 1.61/1.80      (![X1 : $i, X3 : $i]:
% 1.61/1.80         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.61/1.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.61/1.80  thf('85', plain,
% 1.61/1.80      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['83', '84'])).
% 1.61/1.80  thf('86', plain,
% 1.61/1.80      (((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['82', '85'])).
% 1.61/1.80  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.80  thf('88', plain,
% 1.61/1.80      (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['72', '86', '87'])).
% 1.61/1.80  thf('89', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 1.61/1.80          | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('demod', [status(thm)], ['40', '88'])).
% 1.61/1.80  thf('90', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.61/1.80            = (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.61/1.80          | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['61', '62'])).
% 1.61/1.80  thf('91', plain,
% 1.61/1.80      (![X28 : $i, X29 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X28)
% 1.61/1.80          | ~ (v1_relat_1 @ X29)
% 1.61/1.80          | (v1_relat_1 @ (k5_relat_1 @ X28 @ X29)))),
% 1.61/1.80      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.61/1.80  thf('92', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.61/1.80          | ~ (v1_xboole_0 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.61/1.80          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['90', '91'])).
% 1.61/1.80  thf('93', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ k1_xboole_0)
% 1.61/1.80          | ~ (v1_xboole_0 @ X0)
% 1.61/1.80          | (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 1.61/1.80      inference('simplify', [status(thm)], ['92'])).
% 1.61/1.80  thf('94', plain,
% 1.61/1.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.61/1.80  thf('95', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['18', '19'])).
% 1.61/1.80  thf('96', plain,
% 1.61/1.80      (![X0 : $i]: (((k1_xboole_0) = (k4_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['94', '95'])).
% 1.61/1.80  thf('97', plain,
% 1.61/1.80      (![X27 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X27)) | ~ (v1_relat_1 @ X27))),
% 1.61/1.80      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.61/1.80  thf('98', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         ((v1_relat_1 @ k1_xboole_0)
% 1.61/1.80          | ~ (v1_xboole_0 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['96', '97'])).
% 1.61/1.80  thf('99', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 1.61/1.80      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.61/1.80  thf('100', plain,
% 1.61/1.80      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 1.61/1.80      inference('clc', [status(thm)], ['98', '99'])).
% 1.61/1.80  thf('101', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.61/1.80          | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('clc', [status(thm)], ['93', '100'])).
% 1.61/1.80  thf('102', plain,
% 1.61/1.80      (((v1_relat_1 @ k1_xboole_0)
% 1.61/1.80        | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.61/1.80        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['89', '101'])).
% 1.61/1.80  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.80  thf('104', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.80  thf('105', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.61/1.80      inference('demod', [status(thm)], ['102', '103', '104'])).
% 1.61/1.80  thf('106', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.61/1.80           k1_xboole_0)
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('demod', [status(thm)], ['31', '105'])).
% 1.61/1.80  thf('107', plain,
% 1.61/1.80      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['83', '84'])).
% 1.61/1.80  thf('108', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X0)
% 1.61/1.80          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['106', '107'])).
% 1.61/1.80  thf('109', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k1_xboole_0) = (X0))
% 1.61/1.80          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('demod', [status(thm)], ['55', '56'])).
% 1.61/1.80  thf('110', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.61/1.80          | ~ (v1_relat_1 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.61/1.80          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['108', '109'])).
% 1.61/1.80  thf('111', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.80  thf('112', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.61/1.80          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.61/1.80      inference('demod', [status(thm)], ['110', '111'])).
% 1.61/1.80  thf('113', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.61/1.80          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['28', '112'])).
% 1.61/1.80  thf('114', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.61/1.80      inference('demod', [status(thm)], ['102', '103', '104'])).
% 1.61/1.80  thf('115', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X0)
% 1.61/1.80          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('demod', [status(thm)], ['113', '114'])).
% 1.61/1.80  thf('116', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('simplify', [status(thm)], ['115'])).
% 1.61/1.80  thf('117', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         (((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 1.61/1.80          | ~ (v1_xboole_0 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ X1))),
% 1.61/1.80      inference('sup+', [status(thm)], ['27', '116'])).
% 1.61/1.80  thf('118', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X0)
% 1.61/1.80          | ~ (v1_xboole_0 @ X1)
% 1.61/1.80          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))))),
% 1.61/1.80      inference('sup-', [status(thm)], ['26', '117'])).
% 1.61/1.80  thf('119', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.61/1.80          | ~ (v1_relat_1 @ X0)
% 1.61/1.80          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['25', '118'])).
% 1.61/1.80  thf('120', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.80  thf('121', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.61/1.80          | ~ (v1_relat_1 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('demod', [status(thm)], ['119', '120'])).
% 1.61/1.80  thf('122', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X0)
% 1.61/1.80          | ((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 1.61/1.80      inference('simplify', [status(thm)], ['121'])).
% 1.61/1.80  thf(involutiveness_k4_relat_1, axiom,
% 1.61/1.80    (![A:$i]:
% 1.61/1.80     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 1.61/1.80  thf('123', plain,
% 1.61/1.80      (![X30 : $i]:
% 1.61/1.80         (((k4_relat_1 @ (k4_relat_1 @ X30)) = (X30)) | ~ (v1_relat_1 @ X30))),
% 1.61/1.80      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 1.61/1.80  thf('124', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.61/1.80          | ~ (v1_relat_1 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.61/1.80      inference('sup+', [status(thm)], ['122', '123'])).
% 1.61/1.80  thf('125', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['18', '19'])).
% 1.61/1.80  thf('126', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.61/1.80          | ~ (v1_relat_1 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.61/1.80      inference('demod', [status(thm)], ['124', '125'])).
% 1.61/1.80  thf('127', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ k1_xboole_0)
% 1.61/1.80          | ~ (v1_relat_1 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ X0)
% 1.61/1.80          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['0', '126'])).
% 1.61/1.80  thf('128', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.61/1.80      inference('demod', [status(thm)], ['102', '103', '104'])).
% 1.61/1.80  thf('129', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ X0)
% 1.61/1.80          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.61/1.80      inference('demod', [status(thm)], ['127', '128'])).
% 1.61/1.80  thf('130', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('simplify', [status(thm)], ['129'])).
% 1.61/1.80  thf('131', plain,
% 1.61/1.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.61/1.80  thf(t62_relat_1, conjecture,
% 1.61/1.80    (![A:$i]:
% 1.61/1.80     ( ( v1_relat_1 @ A ) =>
% 1.61/1.80       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.61/1.80         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 1.61/1.80  thf(zf_stmt_0, negated_conjecture,
% 1.61/1.80    (~( ![A:$i]:
% 1.61/1.80        ( ( v1_relat_1 @ A ) =>
% 1.61/1.80          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.61/1.80            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 1.61/1.80    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 1.61/1.80  thf('132', plain,
% 1.61/1.80      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 1.61/1.80        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('133', plain,
% 1.61/1.80      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 1.61/1.80         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.61/1.80      inference('split', [status(esa)], ['132'])).
% 1.61/1.80  thf('134', plain,
% 1.61/1.80      ((![X0 : $i]:
% 1.61/1.80          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.61/1.80         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.61/1.80      inference('sup-', [status(thm)], ['131', '133'])).
% 1.61/1.80  thf('135', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('simplify', [status(thm)], ['115'])).
% 1.61/1.80  thf('136', plain,
% 1.61/1.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.61/1.80  thf('137', plain,
% 1.61/1.80      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 1.61/1.80         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.61/1.80      inference('split', [status(esa)], ['132'])).
% 1.61/1.80  thf('138', plain,
% 1.61/1.80      ((![X0 : $i]:
% 1.61/1.80          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.61/1.80         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.61/1.80      inference('sup-', [status(thm)], ['136', '137'])).
% 1.61/1.80  thf('139', plain,
% 1.61/1.80      (((((k1_xboole_0) != (k1_xboole_0))
% 1.61/1.80         | ~ (v1_relat_1 @ sk_A)
% 1.61/1.80         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.61/1.80         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.61/1.80      inference('sup-', [status(thm)], ['135', '138'])).
% 1.61/1.80  thf('140', plain, ((v1_relat_1 @ sk_A)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('141', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.80  thf('142', plain,
% 1.61/1.80      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.61/1.80         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.61/1.80      inference('demod', [status(thm)], ['139', '140', '141'])).
% 1.61/1.80  thf('143', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.61/1.80      inference('simplify', [status(thm)], ['142'])).
% 1.61/1.80  thf('144', plain,
% 1.61/1.80      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 1.61/1.80       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.61/1.80      inference('split', [status(esa)], ['132'])).
% 1.61/1.80  thf('145', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 1.61/1.80      inference('sat_resolution*', [status(thm)], ['143', '144'])).
% 1.61/1.80  thf('146', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.80      inference('simpl_trail', [status(thm)], ['134', '145'])).
% 1.61/1.80  thf('147', plain,
% 1.61/1.80      ((((k1_xboole_0) != (k1_xboole_0))
% 1.61/1.80        | ~ (v1_relat_1 @ sk_A)
% 1.61/1.80        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['130', '146'])).
% 1.61/1.80  thf('148', plain, ((v1_relat_1 @ sk_A)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('149', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.80  thf('150', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['147', '148', '149'])).
% 1.61/1.80  thf('151', plain, ($false), inference('simplify', [status(thm)], ['150'])).
% 1.61/1.80  
% 1.61/1.80  % SZS output end Refutation
% 1.61/1.80  
% 1.67/1.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
