%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wZ1uLebhQH

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:32 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 250 expanded)
%              Number of leaves         :   32 (  91 expanded)
%              Depth                    :   22
%              Number of atoms          :  837 (1774 expanded)
%              Number of equality atoms :   87 ( 201 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_relat_1 @ X31 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X29: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
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

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X36 @ X35 ) )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ ( k1_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('6',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('11',plain,(
    ! [X32: $i] :
      ( ( ( k3_xboole_0 @ X32 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('17',plain,(
    ! [X26: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X22 @ X24 ) @ X23 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('24',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','25'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,(
    ! [X29: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('31',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('32',plain,(
    ! [X29: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('33',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_relat_1 @ X31 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('34',plain,(
    ! [X29: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('35',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('36',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X34 @ X33 ) ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('42',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('43',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X32: $i] :
      ( ( ( k3_xboole_0 @ X32 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ k1_xboole_0 ) ) @ ( k5_xboole_0 @ X0 @ X0 ) ) )
        = ( k5_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('52',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ( ( k2_zfmisc_1 @ X25 @ ( k4_xboole_0 @ X22 @ X24 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X25 @ X22 ) @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('55',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('58',plain,(
    ! [X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['50','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['33','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['32','60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','63'])).

thf('65',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_relat_1 @ X31 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','68'])).

thf('70',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

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

thf('76',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('79',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['76'])).

thf('80',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['76'])).

thf('85',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['77','85'])).

thf('87',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference(simplify,[status(thm)],['89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wZ1uLebhQH
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 358 iterations in 0.146s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.40/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.59  thf(dt_k5_relat_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.40/0.59       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.40/0.59  thf('0', plain,
% 0.40/0.59      (![X30 : $i, X31 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X30)
% 0.40/0.59          | ~ (v1_relat_1 @ X31)
% 0.40/0.59          | (v1_relat_1 @ (k5_relat_1 @ X30 @ X31)))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.40/0.59  thf(cc1_relat_1, axiom,
% 0.40/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.40/0.59  thf('1', plain, (![X29 : $i]: ((v1_relat_1 @ X29) | ~ (v1_xboole_0 @ X29))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.40/0.59  thf(t60_relat_1, axiom,
% 0.40/0.59    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.40/0.59     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.59  thf('2', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.59  thf(t46_relat_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( v1_relat_1 @ B ) =>
% 0.40/0.59           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.40/0.59             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      (![X35 : $i, X36 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X35)
% 0.40/0.59          | ((k1_relat_1 @ (k5_relat_1 @ X36 @ X35)) = (k1_relat_1 @ X36))
% 0.40/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X36) @ (k1_relat_1 @ X35))
% 0.40/0.59          | ~ (v1_relat_1 @ X36))),
% 0.40/0.59      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.59          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.59              = (k1_relat_1 @ k1_xboole_0))
% 0.40/0.59          | ~ (v1_relat_1 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.59  thf('5', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.59  thf('6', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.59          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.40/0.59          | ~ (v1_relat_1 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['1', '7'])).
% 0.40/0.59  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.40/0.59  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X0)
% 0.40/0.59          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.59  thf(t22_relat_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ A ) =>
% 0.40/0.59       ( ( k3_xboole_0 @
% 0.40/0.59           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.40/0.59         ( A ) ) ))).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (![X32 : $i]:
% 0.40/0.59         (((k3_xboole_0 @ X32 @ 
% 0.40/0.59            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))) = (
% 0.40/0.59            X32))
% 0.40/0.59          | ~ (v1_relat_1 @ X32))),
% 0.40/0.59      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.40/0.59            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.40/0.59             (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.40/0.59            = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['10', '11'])).
% 0.40/0.59  thf(t92_xboole_1, axiom,
% 0.40/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.59  thf('13', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.59  thf(t69_enumset1, axiom,
% 0.40/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.59  thf('14', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.40/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.59  thf(t12_setfam_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      (![X27 : $i, X28 : $i]:
% 0.40/0.59         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.40/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.40/0.59  thf(t11_setfam_1, axiom,
% 0.40/0.59    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.40/0.59  thf('17', plain, (![X26 : $i]: ((k1_setfam_1 @ (k1_tarski @ X26)) = (X26))),
% 0.40/0.59      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.40/0.59  thf('18', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.59  thf(t100_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      (![X3 : $i, X4 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X3 @ X4)
% 0.40/0.59           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.40/0.59  thf(t125_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.40/0.59         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.40/0.59       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.40/0.59         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.59         ((k2_zfmisc_1 @ (k4_xboole_0 @ X22 @ X24) @ X23)
% 0.40/0.59           = (k4_xboole_0 @ (k2_zfmisc_1 @ X22 @ X23) @ 
% 0.40/0.59              (k2_zfmisc_1 @ X24 @ X23)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.40/0.59           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['20', '21'])).
% 0.40/0.59  thf('23', plain,
% 0.40/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.40/0.59  thf('24', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['13', '25'])).
% 0.40/0.59  thf(t2_boole, axiom,
% 0.40/0.59    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['12', '26', '27'])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '28'])).
% 0.40/0.59  thf('30', plain, (![X29 : $i]: ((v1_relat_1 @ X29) | ~ (v1_xboole_0 @ X29))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.40/0.59  thf('31', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.59  thf('32', plain, (![X29 : $i]: ((v1_relat_1 @ X29) | ~ (v1_xboole_0 @ X29))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (![X30 : $i, X31 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X30)
% 0.40/0.59          | ~ (v1_relat_1 @ X31)
% 0.40/0.59          | (v1_relat_1 @ (k5_relat_1 @ X30 @ X31)))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.40/0.59  thf('34', plain, (![X29 : $i]: ((v1_relat_1 @ X29) | ~ (v1_xboole_0 @ X29))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.40/0.59  thf('35', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.59  thf(t45_relat_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( v1_relat_1 @ B ) =>
% 0.40/0.59           ( r1_tarski @
% 0.40/0.59             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.40/0.59  thf('36', plain,
% 0.40/0.59      (![X33 : $i, X34 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X33)
% 0.40/0.59          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X34 @ X33)) @ 
% 0.40/0.59             (k2_relat_1 @ X33))
% 0.40/0.59          | ~ (v1_relat_1 @ X34))),
% 0.40/0.59      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.40/0.59           k1_xboole_0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['35', '36'])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.40/0.59             k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['34', '37'])).
% 0.40/0.59  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X0)
% 0.40/0.59          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.40/0.59             k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['38', '39'])).
% 0.40/0.59  thf('41', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.59  thf('42', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.59  thf('43', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.40/0.59      inference('sup+', [status(thm)], ['42', '43'])).
% 0.40/0.59  thf(d10_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      (![X0 : $i, X2 : $i]:
% 0.40/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.59  thf('46', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ X1 @ X1))
% 0.40/0.59          | ((X0) = (k5_xboole_0 @ X1 @ X1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.59  thf('47', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (r1_tarski @ X1 @ k1_xboole_0) | ((X1) = (k5_xboole_0 @ X0 @ X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['41', '46'])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X0)
% 0.40/0.59          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.40/0.59              = (k5_xboole_0 @ X1 @ X1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['40', '47'])).
% 0.40/0.59  thf('49', plain,
% 0.40/0.59      (![X32 : $i]:
% 0.40/0.59         (((k3_xboole_0 @ X32 @ 
% 0.40/0.59            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))) = (
% 0.40/0.59            X32))
% 0.40/0.59          | ~ (v1_relat_1 @ X32))),
% 0.40/0.59      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.40/0.59  thf('50', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (((k3_xboole_0 @ (k5_relat_1 @ X1 @ k1_xboole_0) @ 
% 0.40/0.59            (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ k1_xboole_0)) @ 
% 0.40/0.59             (k5_xboole_0 @ X0 @ X0)))
% 0.40/0.59            = (k5_relat_1 @ X1 @ k1_xboole_0))
% 0.40/0.59          | ~ (v1_relat_1 @ X1)
% 0.40/0.59          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ k1_xboole_0)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['48', '49'])).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.40/0.59         ((k2_zfmisc_1 @ X25 @ (k4_xboole_0 @ X22 @ X24))
% 0.40/0.59           = (k4_xboole_0 @ (k2_zfmisc_1 @ X25 @ X22) @ 
% 0.40/0.59              (k2_zfmisc_1 @ X25 @ X24)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.40/0.59  thf('53', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.40/0.59           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['51', '52'])).
% 0.40/0.59  thf('54', plain,
% 0.40/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.40/0.59  thf('55', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.59  thf('56', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.40/0.59  thf('57', plain,
% 0.40/0.59      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.40/0.59  thf('58', plain,
% 0.40/0.59      (![X1 : $i]:
% 0.40/0.59         (((k1_xboole_0) = (k5_relat_1 @ X1 @ k1_xboole_0))
% 0.40/0.59          | ~ (v1_relat_1 @ X1)
% 0.40/0.59          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['50', '56', '57'])).
% 0.40/0.59  thf('59', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['33', '58'])).
% 0.40/0.59  thf('60', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['59'])).
% 0.40/0.59  thf('61', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['32', '60'])).
% 0.40/0.59  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.59  thf('63', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X0)
% 0.40/0.59          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['61', '62'])).
% 0.40/0.59  thf('64', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (((k1_xboole_0) = (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 0.40/0.59          | ~ (v1_relat_1 @ X1))),
% 0.40/0.59      inference('sup+', [status(thm)], ['31', '63'])).
% 0.40/0.59  thf('65', plain,
% 0.40/0.59      (![X30 : $i, X31 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X30)
% 0.40/0.59          | ~ (v1_relat_1 @ X31)
% 0.40/0.59          | (v1_relat_1 @ (k5_relat_1 @ X30 @ X31)))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.40/0.59  thf('66', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((v1_relat_1 @ k1_xboole_0)
% 0.40/0.59          | ~ (v1_relat_1 @ X1)
% 0.40/0.59          | ~ (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ X1))),
% 0.40/0.59      inference('sup+', [status(thm)], ['64', '65'])).
% 0.40/0.59  thf('67', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ X1)
% 0.40/0.59          | (v1_relat_1 @ k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['66'])).
% 0.40/0.59  thf('68', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0)) | (v1_relat_1 @ k1_xboole_0))),
% 0.40/0.59      inference('condensation', [status(thm)], ['67'])).
% 0.40/0.59  thf('69', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))
% 0.40/0.59          | (v1_relat_1 @ k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['30', '68'])).
% 0.40/0.59  thf('70', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.59  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.59  thf('72', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['70', '71'])).
% 0.40/0.59  thf('73', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.40/0.59      inference('demod', [status(thm)], ['69', '72'])).
% 0.40/0.59  thf('74', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['29', '73'])).
% 0.40/0.59  thf('75', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ X0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['74'])).
% 0.40/0.59  thf(t62_relat_1, conjecture,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ A ) =>
% 0.40/0.59       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.40/0.59         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i]:
% 0.40/0.59        ( ( v1_relat_1 @ A ) =>
% 0.40/0.59          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.40/0.59            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.40/0.59  thf('76', plain,
% 0.40/0.59      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.40/0.59        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('77', plain,
% 0.40/0.59      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.40/0.59         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['76'])).
% 0.40/0.59  thf('78', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X0)
% 0.40/0.59          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['61', '62'])).
% 0.40/0.59  thf('79', plain,
% 0.40/0.59      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.40/0.59         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['76'])).
% 0.40/0.59  thf('80', plain,
% 0.40/0.59      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.40/0.59         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['78', '79'])).
% 0.40/0.59  thf('81', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('82', plain,
% 0.40/0.59      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.40/0.59         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['80', '81'])).
% 0.40/0.59  thf('83', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['82'])).
% 0.40/0.59  thf('84', plain,
% 0.40/0.59      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 0.40/0.59       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.40/0.59      inference('split', [status(esa)], ['76'])).
% 0.40/0.59  thf('85', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.40/0.59      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.40/0.59  thf('86', plain, (((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.40/0.59      inference('simpl_trail', [status(thm)], ['77', '85'])).
% 0.40/0.59  thf('87', plain,
% 0.40/0.59      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['75', '86'])).
% 0.40/0.59  thf('88', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('89', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['87', '88'])).
% 0.40/0.59  thf('90', plain, ($false), inference('simplify', [status(thm)], ['89'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
