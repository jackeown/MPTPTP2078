%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dVxqh2uDKA

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:30 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 257 expanded)
%              Number of leaves         :   24 (  87 expanded)
%              Depth                    :   31
%              Number of atoms          :  736 (1722 expanded)
%              Number of equality atoms :   75 ( 183 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X28 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X27 @ X28 ) ) ) ),
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

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X31 @ X30 ) ) @ ( k2_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

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

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('11',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X28 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('13',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('14',plain,
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

thf('15',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X33 @ X32 ) )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ ( k1_relat_1 @ X32 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('18',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('26',plain,(
    ! [X29: $i] :
      ( ( ( k3_xboole_0 @ X29 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','37'])).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X28 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['45'])).

thf('47',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','49'])).

thf('51',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) )
      | ~ ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X29: $i] :
      ( ( ( k3_xboole_0 @ X29 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','64'])).

thf('66',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['47','48'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('70',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('75',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('80',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('83',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['72','83'])).

thf('85',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    $false ),
    inference(simplify,[status(thm)],['88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dVxqh2uDKA
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:14:24 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.52/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.70  % Solved by: fo/fo7.sh
% 0.52/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.70  % done 560 iterations in 0.262s
% 0.52/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.70  % SZS output start Refutation
% 0.52/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.70  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.52/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.70  thf(dt_k5_relat_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.52/0.70       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.52/0.70  thf('0', plain,
% 0.52/0.70      (![X27 : $i, X28 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X27)
% 0.52/0.70          | ~ (v1_relat_1 @ X28)
% 0.52/0.70          | (v1_relat_1 @ (k5_relat_1 @ X27 @ X28)))),
% 0.52/0.70      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.52/0.70  thf(t60_relat_1, axiom,
% 0.52/0.70    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.52/0.70     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.52/0.70  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.52/0.70  thf(t45_relat_1, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( v1_relat_1 @ A ) =>
% 0.52/0.70       ( ![B:$i]:
% 0.52/0.70         ( ( v1_relat_1 @ B ) =>
% 0.52/0.70           ( r1_tarski @
% 0.52/0.70             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.52/0.70  thf('2', plain,
% 0.52/0.70      (![X30 : $i, X31 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X30)
% 0.52/0.70          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X31 @ X30)) @ 
% 0.52/0.70             (k2_relat_1 @ X30))
% 0.52/0.70          | ~ (v1_relat_1 @ X31))),
% 0.52/0.70      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.52/0.70  thf('3', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.52/0.70           k1_xboole_0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.52/0.70      inference('sup+', [status(thm)], ['1', '2'])).
% 0.52/0.70  thf('4', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.52/0.70  thf(l13_xboole_0, axiom,
% 0.52/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.70  thf('5', plain,
% 0.52/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.70  thf('6', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.52/0.70  thf('7', plain,
% 0.52/0.70      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('sup+', [status(thm)], ['5', '6'])).
% 0.52/0.70  thf(t62_relat_1, conjecture,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( v1_relat_1 @ A ) =>
% 0.52/0.70       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.52/0.70         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.70    (~( ![A:$i]:
% 0.52/0.70        ( ( v1_relat_1 @ A ) =>
% 0.52/0.70          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.52/0.70            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.52/0.70    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.52/0.70  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(cc1_relat_1, axiom,
% 0.52/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.52/0.70  thf('9', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 0.52/0.70      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.52/0.70  thf('10', plain,
% 0.52/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.70  thf('11', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 0.52/0.70      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.52/0.70  thf('12', plain,
% 0.52/0.70      (![X27 : $i, X28 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X27)
% 0.52/0.70          | ~ (v1_relat_1 @ X28)
% 0.52/0.70          | (v1_relat_1 @ (k5_relat_1 @ X27 @ X28)))),
% 0.52/0.70      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.52/0.70  thf('13', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 0.52/0.70      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.52/0.70  thf('14', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.52/0.70  thf(t46_relat_1, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( v1_relat_1 @ A ) =>
% 0.52/0.70       ( ![B:$i]:
% 0.52/0.70         ( ( v1_relat_1 @ B ) =>
% 0.52/0.70           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.52/0.70             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.52/0.70  thf('15', plain,
% 0.52/0.70      (![X32 : $i, X33 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X32)
% 0.52/0.70          | ((k1_relat_1 @ (k5_relat_1 @ X33 @ X32)) = (k1_relat_1 @ X33))
% 0.52/0.70          | ~ (r1_tarski @ (k2_relat_1 @ X33) @ (k1_relat_1 @ X32))
% 0.52/0.70          | ~ (v1_relat_1 @ X33))),
% 0.52/0.70      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.52/0.70  thf('16', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.52/0.70          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.70              = (k1_relat_1 @ k1_xboole_0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.52/0.70  thf('17', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.52/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.70  thf('18', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.52/0.70  thf('19', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ k1_xboole_0)
% 0.52/0.70          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.52/0.70  thf('20', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['13', '19'])).
% 0.52/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.52/0.70  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.70  thf('22', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.52/0.70      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.70  thf(fc4_zfmisc_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.52/0.70  thf('23', plain,
% 0.52/0.70      (![X22 : $i, X23 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ X22) | (v1_xboole_0 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.52/0.70      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.52/0.70  thf('24', plain,
% 0.52/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.70  thf('25', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.70  thf(t22_relat_1, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( v1_relat_1 @ A ) =>
% 0.52/0.70       ( ( k3_xboole_0 @
% 0.52/0.70           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.52/0.70         ( A ) ) ))).
% 0.52/0.70  thf('26', plain,
% 0.52/0.70      (![X29 : $i]:
% 0.52/0.70         (((k3_xboole_0 @ X29 @ 
% 0.52/0.70            (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29))) = (
% 0.52/0.70            X29))
% 0.52/0.70          | ~ (v1_relat_1 @ X29))),
% 0.52/0.70      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.52/0.70  thf('27', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.52/0.70          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('sup+', [status(thm)], ['25', '26'])).
% 0.52/0.70  thf(t2_boole, axiom,
% 0.52/0.70    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.52/0.70  thf('28', plain,
% 0.52/0.70      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.70      inference('cnf', [status(esa)], [t2_boole])).
% 0.52/0.70  thf('29', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((k1_xboole_0) = (X0))
% 0.52/0.70          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['27', '28'])).
% 0.52/0.70  thf('30', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.70          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['22', '29'])).
% 0.52/0.70  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.70  thf('32', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.70          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.52/0.70      inference('demod', [status(thm)], ['30', '31'])).
% 0.52/0.70  thf('33', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.52/0.70          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['12', '32'])).
% 0.52/0.70  thf('34', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['33'])).
% 0.52/0.70  thf('35', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['11', '34'])).
% 0.52/0.70  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.70  thf('37', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.52/0.70      inference('demod', [status(thm)], ['35', '36'])).
% 0.52/0.70  thf('38', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.52/0.70          | ~ (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (v1_relat_1 @ X1))),
% 0.52/0.70      inference('sup+', [status(thm)], ['10', '37'])).
% 0.52/0.70  thf('39', plain,
% 0.52/0.70      (![X27 : $i, X28 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X27)
% 0.52/0.70          | ~ (v1_relat_1 @ X28)
% 0.52/0.70          | (v1_relat_1 @ (k5_relat_1 @ X27 @ X28)))),
% 0.52/0.70      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.52/0.70  thf('40', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((v1_relat_1 @ k1_xboole_0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | ~ (v1_xboole_0 @ X1)
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | ~ (v1_relat_1 @ X1))),
% 0.52/0.70      inference('sup+', [status(thm)], ['38', '39'])).
% 0.52/0.70  thf('41', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X1)
% 0.52/0.70          | ~ (v1_xboole_0 @ X1)
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | (v1_relat_1 @ k1_xboole_0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['40'])).
% 0.52/0.70  thf('42', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ X0)
% 0.52/0.70          | (v1_relat_1 @ k1_xboole_0)
% 0.52/0.70          | ~ (v1_relat_1 @ X1)
% 0.52/0.70          | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['9', '41'])).
% 0.52/0.70  thf('43', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X1)
% 0.52/0.70          | (v1_relat_1 @ k1_xboole_0)
% 0.52/0.70          | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['42'])).
% 0.52/0.70  thf('44', plain,
% 0.52/0.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['8', '43'])).
% 0.52/0.70  thf('45', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((v1_relat_1 @ (k1_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (v1_xboole_0 @ X1))),
% 0.52/0.70      inference('sup+', [status(thm)], ['7', '44'])).
% 0.52/0.70  thf('46', plain,
% 0.52/0.70      (![X0 : $i]: ((v1_relat_1 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('condensation', [status(thm)], ['45'])).
% 0.52/0.70  thf('47', plain,
% 0.52/0.70      (((v1_relat_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.52/0.70      inference('sup+', [status(thm)], ['4', '46'])).
% 0.52/0.70  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.70  thf('49', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.52/0.70      inference('demod', [status(thm)], ['47', '48'])).
% 0.52/0.70  thf('50', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.52/0.70           k1_xboole_0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['3', '49'])).
% 0.52/0.70  thf('51', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.52/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.70  thf(d10_xboole_0, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.70  thf('52', plain,
% 0.52/0.70      (![X1 : $i, X3 : $i]:
% 0.52/0.70         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.52/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.70  thf('53', plain,
% 0.52/0.70      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['51', '52'])).
% 0.52/0.70  thf('54', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['50', '53'])).
% 0.52/0.70  thf(fc3_zfmisc_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.52/0.70  thf('55', plain,
% 0.52/0.70      (![X20 : $i, X21 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21)) | ~ (v1_xboole_0 @ X21))),
% 0.52/0.70      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.52/0.70  thf('56', plain,
% 0.52/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.70  thf('57', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.52/0.70  thf('58', plain,
% 0.52/0.70      (![X29 : $i]:
% 0.52/0.70         (((k3_xboole_0 @ X29 @ 
% 0.52/0.70            (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29))) = (
% 0.52/0.71            X29))
% 0.52/0.71          | ~ (v1_relat_1 @ X29))),
% 0.52/0.71      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.52/0.71  thf('59', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.52/0.71          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['57', '58'])).
% 0.52/0.71  thf('60', plain,
% 0.52/0.71      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.52/0.71  thf('61', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((k1_xboole_0) = (X0))
% 0.52/0.71          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['59', '60'])).
% 0.52/0.71  thf('62', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.52/0.71          | ~ (v1_relat_1 @ X0)
% 0.52/0.71          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.52/0.71          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['54', '61'])).
% 0.52/0.71  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.71  thf('64', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.52/0.71          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.52/0.71      inference('demod', [status(thm)], ['62', '63'])).
% 0.52/0.71  thf('65', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ k1_xboole_0)
% 0.52/0.71          | ~ (v1_relat_1 @ X0)
% 0.52/0.71          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['0', '64'])).
% 0.52/0.71  thf('66', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.52/0.71      inference('demod', [status(thm)], ['47', '48'])).
% 0.52/0.71  thf('67', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['65', '66'])).
% 0.52/0.71  thf('68', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('simplify', [status(thm)], ['67'])).
% 0.52/0.71  thf('69', plain,
% 0.52/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.71  thf('70', plain,
% 0.52/0.71      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.52/0.71        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('71', plain,
% 0.52/0.71      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.71         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.52/0.71      inference('split', [status(esa)], ['70'])).
% 0.52/0.71  thf('72', plain,
% 0.52/0.71      ((![X0 : $i]:
% 0.52/0.71          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.52/0.71         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['69', '71'])).
% 0.52/0.71  thf('73', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.52/0.71      inference('demod', [status(thm)], ['35', '36'])).
% 0.52/0.71  thf('74', plain,
% 0.52/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.71  thf('75', plain,
% 0.52/0.71      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.52/0.71         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('split', [status(esa)], ['70'])).
% 0.52/0.71  thf('76', plain,
% 0.52/0.71      ((![X0 : $i]:
% 0.52/0.71          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.52/0.71         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['74', '75'])).
% 0.52/0.71  thf('77', plain,
% 0.52/0.71      (((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.71         | ~ (v1_relat_1 @ sk_A)
% 0.52/0.71         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.52/0.71         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['73', '76'])).
% 0.52/0.71  thf('78', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.71  thf('80', plain,
% 0.52/0.71      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.71         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.52/0.71  thf('81', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.52/0.71      inference('simplify', [status(thm)], ['80'])).
% 0.52/0.71  thf('82', plain,
% 0.52/0.71      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.52/0.71       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.52/0.71      inference('split', [status(esa)], ['70'])).
% 0.52/0.71  thf('83', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.52/0.71      inference('sat_resolution*', [status(thm)], ['81', '82'])).
% 0.52/0.71  thf('84', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.71      inference('simpl_trail', [status(thm)], ['72', '83'])).
% 0.52/0.71  thf('85', plain,
% 0.52/0.71      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.71        | ~ (v1_relat_1 @ sk_A)
% 0.52/0.71        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['68', '84'])).
% 0.52/0.71  thf('86', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.71  thf('88', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.52/0.71      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.52/0.71  thf('89', plain, ($false), inference('simplify', [status(thm)], ['88'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
