%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wJ7l0DDlVu

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:29 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 328 expanded)
%              Number of leaves         :   24 ( 109 expanded)
%              Depth                    :   29
%              Number of atoms          :  824 (2171 expanded)
%              Number of equality atoms :   71 ( 178 expanded)
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
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X33 @ X32 ) ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

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

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X28 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('8',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X31 @ X30 ) ) @ ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('19',plain,(
    ! [X29: $i] :
      ( ( ( k3_xboole_0 @ X29 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('37',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('38',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X28 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X29: $i] :
      ( ( ( k3_xboole_0 @ X29 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','54'])).

thf('56',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X28 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['61'])).

thf('63',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('67',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) )
      | ~ ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X29: $i] :
      ( ( ( k3_xboole_0 @ X29 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','76'])).

thf('78',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','62'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('82',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('87',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['82'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['82'])).

thf('95',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['84','95'])).

thf('97',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('100',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    $false ),
    inference(simplify,[status(thm)],['100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wJ7l0DDlVu
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 330 iterations in 0.185s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.64  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.64  thf(dt_k5_relat_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.47/0.64       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.47/0.64  thf('0', plain,
% 0.47/0.64      (![X27 : $i, X28 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X27)
% 0.47/0.64          | ~ (v1_relat_1 @ X28)
% 0.47/0.64          | (v1_relat_1 @ (k5_relat_1 @ X27 @ X28)))),
% 0.47/0.64      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.47/0.64  thf(t60_relat_1, axiom,
% 0.47/0.64    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.47/0.64     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.64  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.64  thf(t45_relat_1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ A ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( v1_relat_1 @ B ) =>
% 0.47/0.64           ( r1_tarski @
% 0.47/0.64             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.47/0.64  thf('2', plain,
% 0.47/0.64      (![X32 : $i, X33 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X32)
% 0.47/0.64          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X33 @ X32)) @ 
% 0.47/0.64             (k2_relat_1 @ X32))
% 0.47/0.64          | ~ (v1_relat_1 @ X33))),
% 0.47/0.64      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.47/0.64  thf('3', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.47/0.64           k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['1', '2'])).
% 0.47/0.64  thf(t62_relat_1, conjecture,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ A ) =>
% 0.47/0.64       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.47/0.64         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i]:
% 0.47/0.64        ( ( v1_relat_1 @ A ) =>
% 0.47/0.64          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.47/0.64            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.47/0.64  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(cc1_relat_1, axiom,
% 0.47/0.64    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.47/0.64  thf('5', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 0.47/0.64      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.47/0.64  thf('6', plain,
% 0.47/0.64      (![X27 : $i, X28 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X27)
% 0.47/0.64          | ~ (v1_relat_1 @ X28)
% 0.47/0.64          | (v1_relat_1 @ (k5_relat_1 @ X27 @ X28)))),
% 0.47/0.64      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.47/0.64  thf('7', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 0.47/0.64      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.47/0.64  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.64  thf(t44_relat_1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ A ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( v1_relat_1 @ B ) =>
% 0.47/0.64           ( r1_tarski @
% 0.47/0.64             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.47/0.64  thf('9', plain,
% 0.47/0.64      (![X30 : $i, X31 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X30)
% 0.47/0.64          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X31 @ X30)) @ 
% 0.47/0.64             (k1_relat_1 @ X31))
% 0.47/0.64          | ~ (v1_relat_1 @ X31))),
% 0.47/0.64      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.47/0.64           k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['8', '9'])).
% 0.47/0.64  thf('11', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.47/0.64             k1_xboole_0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['7', '10'])).
% 0.47/0.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.64  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.64  thf('13', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.47/0.64             k1_xboole_0))),
% 0.47/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.64  thf('14', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.47/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.64  thf(d10_xboole_0, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.64  thf('15', plain,
% 0.47/0.64      (![X1 : $i, X3 : $i]:
% 0.47/0.64         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.47/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.64  thf('16', plain,
% 0.47/0.64      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.64  thf('17', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['13', '16'])).
% 0.47/0.64  thf(fc4_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      (![X22 : $i, X23 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ X22) | (v1_xboole_0 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.47/0.64      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.47/0.64  thf(t22_relat_1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ A ) =>
% 0.47/0.64       ( ( k3_xboole_0 @
% 0.47/0.64           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.47/0.64         ( A ) ) ))).
% 0.47/0.64  thf('19', plain,
% 0.47/0.64      (![X29 : $i]:
% 0.47/0.64         (((k3_xboole_0 @ X29 @ 
% 0.47/0.64            (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29))) = (
% 0.47/0.64            X29))
% 0.47/0.64          | ~ (v1_relat_1 @ X29))),
% 0.47/0.64      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.47/0.64  thf(l13_xboole_0, axiom,
% 0.47/0.64    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.64  thf('20', plain,
% 0.47/0.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.64      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.64  thf(t2_boole, axiom,
% 0.47/0.64    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.64  thf('21', plain,
% 0.47/0.64      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.64  thf('22', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['20', '21'])).
% 0.47/0.64  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.64  thf('24', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['22', '23'])).
% 0.47/0.64  thf('25', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((v1_xboole_0 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | ~ (v1_xboole_0 @ 
% 0.47/0.64               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.47/0.64      inference('sup+', [status(thm)], ['19', '24'])).
% 0.47/0.64  thf('26', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | (v1_xboole_0 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['18', '25'])).
% 0.47/0.64  thf('27', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.64          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['17', '26'])).
% 0.47/0.64  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.64  thf('29', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.64          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['27', '28'])).
% 0.47/0.64  thf('30', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.64          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['6', '29'])).
% 0.47/0.64  thf('31', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.64          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['30'])).
% 0.47/0.64  thf('32', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['5', '31'])).
% 0.47/0.64  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.64  thf('34', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['32', '33'])).
% 0.47/0.64  thf('35', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 0.47/0.64      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.47/0.64  thf('36', plain,
% 0.47/0.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.64      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.64  thf('37', plain, (![X26 : $i]: ((v1_relat_1 @ X26) | ~ (v1_xboole_0 @ X26))),
% 0.47/0.64      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.47/0.64  thf('38', plain,
% 0.47/0.64      (![X27 : $i, X28 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X27)
% 0.47/0.64          | ~ (v1_relat_1 @ X28)
% 0.47/0.64          | (v1_relat_1 @ (k5_relat_1 @ X27 @ X28)))),
% 0.47/0.64      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.47/0.64  thf('39', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['13', '16'])).
% 0.47/0.64  thf('40', plain,
% 0.47/0.64      (![X22 : $i, X23 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ X22) | (v1_xboole_0 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.47/0.64      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.47/0.64  thf('41', plain,
% 0.47/0.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.64      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.64  thf('42', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.64  thf('43', plain,
% 0.47/0.64      (![X29 : $i]:
% 0.47/0.64         (((k3_xboole_0 @ X29 @ 
% 0.47/0.64            (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29))) = (
% 0.47/0.64            X29))
% 0.47/0.64          | ~ (v1_relat_1 @ X29))),
% 0.47/0.64      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.47/0.64  thf('44', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.47/0.64          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['42', '43'])).
% 0.47/0.64  thf('45', plain,
% 0.47/0.64      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.64  thf('46', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k1_xboole_0) = (X0))
% 0.47/0.64          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('demod', [status(thm)], ['44', '45'])).
% 0.47/0.64  thf('47', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.64          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['39', '46'])).
% 0.47/0.64  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.64  thf('49', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.64          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.47/0.64  thf('50', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.64          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['38', '49'])).
% 0.47/0.64  thf('51', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.64          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['50'])).
% 0.47/0.64  thf('52', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['37', '51'])).
% 0.47/0.64  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.64  thf('54', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.64  thf('55', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.47/0.64          | ~ (v1_xboole_0 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ X1))),
% 0.47/0.64      inference('sup+', [status(thm)], ['36', '54'])).
% 0.47/0.64  thf('56', plain,
% 0.47/0.64      (![X27 : $i, X28 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X27)
% 0.47/0.64          | ~ (v1_relat_1 @ X28)
% 0.47/0.64          | (v1_relat_1 @ (k5_relat_1 @ X27 @ X28)))),
% 0.47/0.64      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.47/0.64  thf('57', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((v1_relat_1 @ k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | ~ (v1_xboole_0 @ X1)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ X1))),
% 0.47/0.64      inference('sup+', [status(thm)], ['55', '56'])).
% 0.47/0.64  thf('58', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X1)
% 0.47/0.64          | ~ (v1_xboole_0 @ X1)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | (v1_relat_1 @ k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['57'])).
% 0.47/0.64  thf('59', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ X0)
% 0.47/0.64          | (v1_relat_1 @ k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X1)
% 0.47/0.64          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['35', '58'])).
% 0.47/0.64  thf('60', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X1)
% 0.47/0.64          | (v1_relat_1 @ k1_xboole_0)
% 0.47/0.64          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['59'])).
% 0.47/0.64  thf('61', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | (v1_relat_1 @ k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['34', '60'])).
% 0.47/0.64  thf('62', plain,
% 0.47/0.64      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.47/0.64      inference('condensation', [status(thm)], ['61'])).
% 0.47/0.64  thf('63', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.64      inference('sup-', [status(thm)], ['4', '62'])).
% 0.47/0.64  thf('64', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.47/0.64           k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('demod', [status(thm)], ['3', '63'])).
% 0.47/0.64  thf('65', plain,
% 0.47/0.64      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.64  thf('66', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['64', '65'])).
% 0.47/0.64  thf(fc3_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.47/0.64  thf('67', plain,
% 0.47/0.64      (![X20 : $i, X21 : $i]:
% 0.47/0.64         ((v1_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21)) | ~ (v1_xboole_0 @ X21))),
% 0.47/0.64      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.47/0.64  thf('68', plain,
% 0.47/0.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.64      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.64  thf('69', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['67', '68'])).
% 0.47/0.64  thf('70', plain,
% 0.47/0.64      (![X29 : $i]:
% 0.47/0.64         (((k3_xboole_0 @ X29 @ 
% 0.47/0.64            (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29))) = (
% 0.47/0.64            X29))
% 0.47/0.64          | ~ (v1_relat_1 @ X29))),
% 0.47/0.64      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.47/0.64  thf('71', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.47/0.64          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['69', '70'])).
% 0.47/0.64  thf('72', plain,
% 0.47/0.64      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.64  thf('73', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k1_xboole_0) = (X0))
% 0.47/0.64          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('demod', [status(thm)], ['71', '72'])).
% 0.47/0.64  thf('74', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.64          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['66', '73'])).
% 0.47/0.64  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.64  thf('76', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.64          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['74', '75'])).
% 0.47/0.64  thf('77', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['0', '76'])).
% 0.47/0.64  thf('78', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.64      inference('sup-', [status(thm)], ['4', '62'])).
% 0.47/0.64  thf('79', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('demod', [status(thm)], ['77', '78'])).
% 0.47/0.64  thf('80', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['79'])).
% 0.47/0.64  thf('81', plain,
% 0.47/0.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.64      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.64  thf('82', plain,
% 0.47/0.64      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.47/0.64        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('83', plain,
% 0.47/0.64      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.47/0.64         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['82'])).
% 0.47/0.64  thf('84', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.47/0.64         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['81', '83'])).
% 0.47/0.64  thf('85', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.64  thf('86', plain,
% 0.47/0.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.64      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.64  thf('87', plain,
% 0.47/0.64      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.47/0.64         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.64      inference('split', [status(esa)], ['82'])).
% 0.47/0.64  thf('88', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.47/0.64         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['86', '87'])).
% 0.47/0.64  thf('89', plain,
% 0.47/0.64      (((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.64         | ~ (v1_relat_1 @ sk_A)
% 0.47/0.64         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.47/0.64         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['85', '88'])).
% 0.47/0.64  thf('90', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.64  thf('92', plain,
% 0.47/0.64      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.47/0.64         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.64      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.47/0.64  thf('93', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['92'])).
% 0.47/0.64  thf('94', plain,
% 0.47/0.64      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.47/0.64       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.64      inference('split', [status(esa)], ['82'])).
% 0.47/0.64  thf('95', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sat_resolution*', [status(thm)], ['93', '94'])).
% 0.47/0.64  thf('96', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['84', '95'])).
% 0.47/0.64  thf('97', plain,
% 0.47/0.64      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.64        | ~ (v1_relat_1 @ sk_A)
% 0.47/0.64        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['80', '96'])).
% 0.47/0.64  thf('98', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('99', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.64  thf('100', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.47/0.64      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.47/0.64  thf('101', plain, ($false), inference('simplify', [status(thm)], ['100'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
