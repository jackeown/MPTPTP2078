%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TabWbyvnZ0

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:36 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 717 expanded)
%              Number of leaves         :   33 ( 241 expanded)
%              Depth                    :   37
%              Number of atoms          : 1014 (4825 expanded)
%              Number of equality atoms :  113 ( 512 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v1_relat_1 @ X30 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X29 @ X30 ) ) ) ),
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

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('9',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','4'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('13',plain,(
    ! [X32: $i] :
      ( ( ( k3_xboole_0 @ X32 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

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

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('22',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('23',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('24',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('26',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v1_relat_1 @ X30 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('27',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('28',plain,
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

thf('29',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X36 @ X35 ) )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ ( k1_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('38',plain,(
    ! [X32: $i] :
      ( ( ( k3_xboole_0 @ X32 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','49'])).

thf('51',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v1_relat_1 @ X30 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','55'])).

thf('57',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','56'])).

thf('58',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['16','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('65',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','69'])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X34 @ X33 ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X34 ) @ ( k4_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('73',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('74',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('75',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X34 @ X33 ) )
        = ( k4_xboole_0 @ ( k4_relat_1 @ X34 ) @ ( k4_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('80',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','56'])).

thf('81',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79','80'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('82',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X38 @ X37 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X37 ) @ ( k4_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('83',plain,(
    ! [X28: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','49'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','56'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('92',plain,(
    ! [X31: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X31 ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','95'])).

thf('97',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','56'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('101',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['101'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('105',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('106',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['101'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('111',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['101'])).

thf('114',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['103','114'])).

thf('116',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('119',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    $false ),
    inference(simplify,[status(thm)],['119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TabWbyvnZ0
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:56:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.22/0.35  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 1.65/1.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.65/1.84  % Solved by: fo/fo7.sh
% 1.65/1.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.84  % done 2302 iterations in 1.354s
% 1.65/1.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.65/1.84  % SZS output start Refutation
% 1.65/1.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.65/1.84  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.65/1.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.65/1.84  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.65/1.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.65/1.84  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.65/1.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.65/1.84  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.65/1.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.65/1.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.65/1.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.65/1.84  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.65/1.84  thf(dt_k5_relat_1, axiom,
% 1.65/1.84    (![A:$i,B:$i]:
% 1.65/1.84     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.65/1.84       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.65/1.84  thf('0', plain,
% 1.65/1.84      (![X29 : $i, X30 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X29)
% 1.65/1.84          | ~ (v1_relat_1 @ X30)
% 1.65/1.84          | (v1_relat_1 @ (k5_relat_1 @ X29 @ X30)))),
% 1.65/1.84      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.65/1.84  thf(t92_xboole_1, axiom,
% 1.65/1.84    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.65/1.84  thf('1', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 1.65/1.84      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.65/1.84  thf(idempotence_k3_xboole_0, axiom,
% 1.65/1.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.65/1.84  thf('2', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.65/1.84      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.65/1.84  thf(t100_xboole_1, axiom,
% 1.65/1.84    (![A:$i,B:$i]:
% 1.65/1.84     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.65/1.84  thf('3', plain,
% 1.65/1.84      (![X2 : $i, X3 : $i]:
% 1.65/1.84         ((k4_xboole_0 @ X2 @ X3)
% 1.65/1.84           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.65/1.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.65/1.84  thf('4', plain,
% 1.65/1.84      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.65/1.84      inference('sup+', [status(thm)], ['2', '3'])).
% 1.65/1.84  thf('5', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 1.65/1.84      inference('demod', [status(thm)], ['1', '4'])).
% 1.65/1.84  thf(l13_xboole_0, axiom,
% 1.65/1.84    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.65/1.84  thf('6', plain,
% 1.65/1.84      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.65/1.84  thf('7', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         (((X1) = (k4_xboole_0 @ X0 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.84      inference('sup+', [status(thm)], ['5', '6'])).
% 1.65/1.84  thf(fc4_zfmisc_1, axiom,
% 1.65/1.84    (![A:$i,B:$i]:
% 1.65/1.84     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 1.65/1.84  thf('8', plain,
% 1.65/1.84      (![X21 : $i, X22 : $i]:
% 1.65/1.84         (~ (v1_xboole_0 @ X21) | (v1_xboole_0 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 1.65/1.84      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 1.65/1.84  thf('9', plain,
% 1.65/1.84      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.65/1.84  thf('10', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.65/1.84      inference('sup-', [status(thm)], ['8', '9'])).
% 1.65/1.84  thf('11', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 1.65/1.84      inference('demod', [status(thm)], ['1', '4'])).
% 1.65/1.84  thf(t60_relat_1, axiom,
% 1.65/1.84    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.65/1.84     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.65/1.84  thf('12', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.84      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.65/1.84  thf(t22_relat_1, axiom,
% 1.65/1.84    (![A:$i]:
% 1.65/1.84     ( ( v1_relat_1 @ A ) =>
% 1.65/1.84       ( ( k3_xboole_0 @
% 1.65/1.84           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 1.65/1.84         ( A ) ) ))).
% 1.65/1.84  thf('13', plain,
% 1.65/1.84      (![X32 : $i]:
% 1.65/1.84         (((k3_xboole_0 @ X32 @ 
% 1.65/1.84            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))) = (
% 1.65/1.84            X32))
% 1.65/1.84          | ~ (v1_relat_1 @ X32))),
% 1.65/1.84      inference('cnf', [status(esa)], [t22_relat_1])).
% 1.65/1.84  thf('14', plain,
% 1.65/1.84      ((((k3_xboole_0 @ k1_xboole_0 @ 
% 1.65/1.84          (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 1.65/1.84          = (k1_xboole_0))
% 1.65/1.84        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.65/1.84      inference('sup+', [status(thm)], ['12', '13'])).
% 1.65/1.84  thf('15', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.84      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.65/1.84  thf('16', plain,
% 1.65/1.84      ((((k3_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.65/1.84          = (k1_xboole_0))
% 1.65/1.84        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.65/1.84      inference('demod', [status(thm)], ['14', '15'])).
% 1.65/1.84  thf(t62_relat_1, conjecture,
% 1.65/1.84    (![A:$i]:
% 1.65/1.84     ( ( v1_relat_1 @ A ) =>
% 1.65/1.84       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.65/1.84         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 1.65/1.84  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.84    (~( ![A:$i]:
% 1.65/1.84        ( ( v1_relat_1 @ A ) =>
% 1.65/1.84          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.65/1.84            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 1.65/1.84    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 1.65/1.84  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('18', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 1.65/1.84      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.65/1.84  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.65/1.84  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.84  thf('20', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 1.65/1.84      inference('sup+', [status(thm)], ['18', '19'])).
% 1.65/1.84  thf('21', plain,
% 1.65/1.84      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.65/1.84      inference('sup+', [status(thm)], ['2', '3'])).
% 1.65/1.84  thf('22', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 1.65/1.84      inference('demod', [status(thm)], ['20', '21'])).
% 1.65/1.84  thf(cc1_relat_1, axiom,
% 1.65/1.84    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 1.65/1.84  thf('23', plain, (![X27 : $i]: ((v1_relat_1 @ X27) | ~ (v1_xboole_0 @ X27))),
% 1.65/1.84      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.65/1.84  thf('24', plain,
% 1.65/1.84      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.65/1.84  thf('25', plain, (![X27 : $i]: ((v1_relat_1 @ X27) | ~ (v1_xboole_0 @ X27))),
% 1.65/1.84      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.65/1.84  thf('26', plain,
% 1.65/1.84      (![X29 : $i, X30 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X29)
% 1.65/1.84          | ~ (v1_relat_1 @ X30)
% 1.65/1.84          | (v1_relat_1 @ (k5_relat_1 @ X29 @ X30)))),
% 1.65/1.84      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.65/1.84  thf('27', plain, (![X27 : $i]: ((v1_relat_1 @ X27) | ~ (v1_xboole_0 @ X27))),
% 1.65/1.84      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.65/1.84  thf('28', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.84      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.65/1.84  thf(t46_relat_1, axiom,
% 1.65/1.84    (![A:$i]:
% 1.65/1.84     ( ( v1_relat_1 @ A ) =>
% 1.65/1.84       ( ![B:$i]:
% 1.65/1.84         ( ( v1_relat_1 @ B ) =>
% 1.65/1.84           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 1.65/1.84             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 1.65/1.84  thf('29', plain,
% 1.65/1.84      (![X35 : $i, X36 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X35)
% 1.65/1.84          | ((k1_relat_1 @ (k5_relat_1 @ X36 @ X35)) = (k1_relat_1 @ X36))
% 1.65/1.84          | ~ (r1_tarski @ (k2_relat_1 @ X36) @ (k1_relat_1 @ X35))
% 1.65/1.84          | ~ (v1_relat_1 @ X36))),
% 1.65/1.84      inference('cnf', [status(esa)], [t46_relat_1])).
% 1.65/1.84  thf('30', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.65/1.84          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.65/1.84              = (k1_relat_1 @ k1_xboole_0))
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('sup-', [status(thm)], ['28', '29'])).
% 1.65/1.84  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.65/1.84  thf('31', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.65/1.84      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.65/1.84  thf('32', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.84      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.65/1.84  thf('33', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ k1_xboole_0)
% 1.65/1.84          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.65/1.84  thf('34', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 1.65/1.84      inference('sup-', [status(thm)], ['27', '33'])).
% 1.65/1.84  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.84  thf('36', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X0)
% 1.65/1.84          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 1.65/1.84      inference('demod', [status(thm)], ['34', '35'])).
% 1.65/1.84  thf('37', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.65/1.84      inference('sup-', [status(thm)], ['8', '9'])).
% 1.65/1.84  thf('38', plain,
% 1.65/1.84      (![X32 : $i]:
% 1.65/1.84         (((k3_xboole_0 @ X32 @ 
% 1.65/1.84            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))) = (
% 1.65/1.84            X32))
% 1.65/1.84          | ~ (v1_relat_1 @ X32))),
% 1.65/1.84      inference('cnf', [status(esa)], [t22_relat_1])).
% 1.65/1.84  thf('39', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 1.65/1.84          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('sup+', [status(thm)], ['37', '38'])).
% 1.65/1.84  thf(t2_boole, axiom,
% 1.65/1.84    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.65/1.84  thf('40', plain,
% 1.65/1.84      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.84      inference('cnf', [status(esa)], [t2_boole])).
% 1.65/1.84  thf('41', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (((k1_xboole_0) = (X0))
% 1.65/1.84          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('demod', [status(thm)], ['39', '40'])).
% 1.65/1.84  thf('42', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.65/1.84          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.65/1.84      inference('sup-', [status(thm)], ['36', '41'])).
% 1.65/1.84  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.84  thf('44', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.65/1.84          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.65/1.84      inference('demod', [status(thm)], ['42', '43'])).
% 1.65/1.84  thf('45', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.65/1.84          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('sup-', [status(thm)], ['26', '44'])).
% 1.65/1.84  thf('46', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('simplify', [status(thm)], ['45'])).
% 1.65/1.84  thf('47', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.65/1.84      inference('sup-', [status(thm)], ['25', '46'])).
% 1.65/1.84  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.84  thf('49', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X0)
% 1.65/1.84          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.65/1.84      inference('demod', [status(thm)], ['47', '48'])).
% 1.65/1.84  thf('50', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         (((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 1.65/1.84          | ~ (v1_xboole_0 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ X1))),
% 1.65/1.84      inference('sup+', [status(thm)], ['24', '49'])).
% 1.65/1.84  thf('51', plain,
% 1.65/1.84      (![X29 : $i, X30 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X29)
% 1.65/1.84          | ~ (v1_relat_1 @ X30)
% 1.65/1.84          | (v1_relat_1 @ (k5_relat_1 @ X29 @ X30)))),
% 1.65/1.84      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.65/1.84  thf('52', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         ((v1_relat_1 @ k1_xboole_0)
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_xboole_0 @ X1)
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ X1))),
% 1.65/1.84      inference('sup+', [status(thm)], ['50', '51'])).
% 1.65/1.84  thf('53', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X1)
% 1.65/1.84          | ~ (v1_xboole_0 @ X1)
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | (v1_relat_1 @ k1_xboole_0))),
% 1.65/1.84      inference('simplify', [status(thm)], ['52'])).
% 1.65/1.84  thf('54', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         (~ (v1_xboole_0 @ X0)
% 1.65/1.84          | (v1_relat_1 @ k1_xboole_0)
% 1.65/1.84          | ~ (v1_relat_1 @ X1)
% 1.65/1.84          | ~ (v1_xboole_0 @ X0))),
% 1.65/1.84      inference('sup-', [status(thm)], ['23', '53'])).
% 1.65/1.84  thf('55', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X1)
% 1.65/1.84          | (v1_relat_1 @ k1_xboole_0)
% 1.65/1.84          | ~ (v1_xboole_0 @ X0))),
% 1.65/1.84      inference('simplify', [status(thm)], ['54'])).
% 1.65/1.84  thf('56', plain,
% 1.65/1.84      (![X1 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X1))),
% 1.65/1.84      inference('sup-', [status(thm)], ['22', '55'])).
% 1.65/1.84  thf('57', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.65/1.84      inference('sup-', [status(thm)], ['17', '56'])).
% 1.65/1.84  thf('58', plain,
% 1.65/1.84      (((k3_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.65/1.84         = (k1_xboole_0))),
% 1.65/1.84      inference('demod', [status(thm)], ['16', '57'])).
% 1.65/1.84  thf('59', plain,
% 1.65/1.84      (![X2 : $i, X3 : $i]:
% 1.65/1.84         ((k4_xboole_0 @ X2 @ X3)
% 1.65/1.84           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.65/1.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.65/1.84  thf('60', plain,
% 1.65/1.84      (((k4_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.65/1.84         = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.65/1.84      inference('sup+', [status(thm)], ['58', '59'])).
% 1.65/1.84  thf('61', plain,
% 1.65/1.84      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.84      inference('cnf', [status(esa)], [t2_boole])).
% 1.65/1.84  thf('62', plain,
% 1.65/1.84      (![X2 : $i, X3 : $i]:
% 1.65/1.84         ((k4_xboole_0 @ X2 @ X3)
% 1.65/1.84           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.65/1.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.65/1.84  thf('63', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.65/1.84      inference('sup+', [status(thm)], ['61', '62'])).
% 1.65/1.84  thf('64', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 1.65/1.84      inference('demod', [status(thm)], ['1', '4'])).
% 1.65/1.84  thf('65', plain,
% 1.65/1.84      (((k4_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.65/1.84         = (k1_xboole_0))),
% 1.65/1.84      inference('demod', [status(thm)], ['60', '63', '64'])).
% 1.65/1.84  thf('66', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 1.65/1.84           (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.65/1.84      inference('sup+', [status(thm)], ['11', '65'])).
% 1.65/1.84  thf('67', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 1.65/1.84            = (k1_xboole_0))
% 1.65/1.84          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.65/1.84      inference('sup+', [status(thm)], ['10', '66'])).
% 1.65/1.84  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.84  thf('69', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.84      inference('demod', [status(thm)], ['67', '68'])).
% 1.65/1.84  thf('70', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (((k4_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 1.65/1.84          | ~ (v1_xboole_0 @ X0))),
% 1.65/1.84      inference('sup+', [status(thm)], ['7', '69'])).
% 1.65/1.84  thf('71', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 1.65/1.84      inference('demod', [status(thm)], ['1', '4'])).
% 1.65/1.84  thf(t41_relat_1, axiom,
% 1.65/1.84    (![A:$i]:
% 1.65/1.84     ( ( v1_relat_1 @ A ) =>
% 1.65/1.84       ( ![B:$i]:
% 1.65/1.84         ( ( v1_relat_1 @ B ) =>
% 1.65/1.84           ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) ) =
% 1.65/1.84             ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) ))).
% 1.65/1.84  thf('72', plain,
% 1.65/1.84      (![X33 : $i, X34 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X33)
% 1.65/1.84          | ((k4_relat_1 @ (k6_subset_1 @ X34 @ X33))
% 1.65/1.84              = (k6_subset_1 @ (k4_relat_1 @ X34) @ (k4_relat_1 @ X33)))
% 1.65/1.84          | ~ (v1_relat_1 @ X34))),
% 1.65/1.84      inference('cnf', [status(esa)], [t41_relat_1])).
% 1.65/1.84  thf(redefinition_k6_subset_1, axiom,
% 1.65/1.84    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.65/1.84  thf('73', plain,
% 1.65/1.84      (![X23 : $i, X24 : $i]:
% 1.65/1.84         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 1.65/1.84      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.65/1.84  thf('74', plain,
% 1.65/1.84      (![X23 : $i, X24 : $i]:
% 1.65/1.84         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 1.65/1.84      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.65/1.84  thf('75', plain,
% 1.65/1.84      (![X33 : $i, X34 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X33)
% 1.65/1.84          | ((k4_relat_1 @ (k4_xboole_0 @ X34 @ X33))
% 1.65/1.84              = (k4_xboole_0 @ (k4_relat_1 @ X34) @ (k4_relat_1 @ X33)))
% 1.65/1.84          | ~ (v1_relat_1 @ X34))),
% 1.65/1.84      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.65/1.84  thf('76', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('sup+', [status(thm)], ['71', '75'])).
% 1.65/1.84  thf('77', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X0)
% 1.65/1.84          | ((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0)))),
% 1.65/1.84      inference('simplify', [status(thm)], ['76'])).
% 1.65/1.84  thf('78', plain,
% 1.65/1.84      ((((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 1.65/1.84        | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.84        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.65/1.84      inference('sup+', [status(thm)], ['70', '77'])).
% 1.65/1.84  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.84  thf('80', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.65/1.84      inference('sup-', [status(thm)], ['17', '56'])).
% 1.65/1.84  thf('81', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.84      inference('demod', [status(thm)], ['78', '79', '80'])).
% 1.65/1.84  thf(t54_relat_1, axiom,
% 1.65/1.84    (![A:$i]:
% 1.65/1.84     ( ( v1_relat_1 @ A ) =>
% 1.65/1.84       ( ![B:$i]:
% 1.65/1.84         ( ( v1_relat_1 @ B ) =>
% 1.65/1.84           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.65/1.84             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 1.65/1.84  thf('82', plain,
% 1.65/1.84      (![X37 : $i, X38 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X37)
% 1.65/1.84          | ((k4_relat_1 @ (k5_relat_1 @ X38 @ X37))
% 1.65/1.84              = (k5_relat_1 @ (k4_relat_1 @ X37) @ (k4_relat_1 @ X38)))
% 1.65/1.84          | ~ (v1_relat_1 @ X38))),
% 1.65/1.84      inference('cnf', [status(esa)], [t54_relat_1])).
% 1.65/1.84  thf(dt_k4_relat_1, axiom,
% 1.65/1.84    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 1.65/1.84  thf('83', plain,
% 1.65/1.84      (![X28 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X28)) | ~ (v1_relat_1 @ X28))),
% 1.65/1.84      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.65/1.84  thf('84', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         (((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 1.65/1.84          | ~ (v1_xboole_0 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ X1))),
% 1.65/1.84      inference('sup+', [status(thm)], ['24', '49'])).
% 1.65/1.84  thf('85', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_xboole_0 @ X1)
% 1.65/1.84          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))))),
% 1.65/1.84      inference('sup-', [status(thm)], ['83', '84'])).
% 1.65/1.84  thf('86', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.65/1.84          | ~ (v1_relat_1 @ X1)
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ X1))),
% 1.65/1.84      inference('sup+', [status(thm)], ['82', '85'])).
% 1.65/1.84  thf('87', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         (~ (v1_xboole_0 @ (k4_relat_1 @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ X1)
% 1.65/1.84          | ((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 1.65/1.84      inference('simplify', [status(thm)], ['86'])).
% 1.65/1.84  thf('88', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.84          | ((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.65/1.84      inference('sup-', [status(thm)], ['81', '87'])).
% 1.65/1.84  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.84  thf('90', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.65/1.84      inference('sup-', [status(thm)], ['17', '56'])).
% 1.65/1.84  thf('91', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('demod', [status(thm)], ['88', '89', '90'])).
% 1.65/1.84  thf(involutiveness_k4_relat_1, axiom,
% 1.65/1.84    (![A:$i]:
% 1.65/1.84     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 1.65/1.84  thf('92', plain,
% 1.65/1.84      (![X31 : $i]:
% 1.65/1.84         (((k4_relat_1 @ (k4_relat_1 @ X31)) = (X31)) | ~ (v1_relat_1 @ X31))),
% 1.65/1.84      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 1.65/1.84  thf('93', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.65/1.84      inference('sup+', [status(thm)], ['91', '92'])).
% 1.65/1.84  thf('94', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.84      inference('demod', [status(thm)], ['78', '79', '80'])).
% 1.65/1.84  thf('95', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.65/1.84      inference('demod', [status(thm)], ['93', '94'])).
% 1.65/1.84  thf('96', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ k1_xboole_0)
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.65/1.84      inference('sup-', [status(thm)], ['0', '95'])).
% 1.65/1.84  thf('97', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.65/1.84      inference('sup-', [status(thm)], ['17', '56'])).
% 1.65/1.84  thf('98', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.65/1.84      inference('demod', [status(thm)], ['96', '97'])).
% 1.65/1.84  thf('99', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('simplify', [status(thm)], ['98'])).
% 1.65/1.84  thf('100', plain,
% 1.65/1.84      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.65/1.84  thf('101', plain,
% 1.65/1.84      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 1.65/1.84        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('102', plain,
% 1.65/1.84      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 1.65/1.84         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.65/1.84      inference('split', [status(esa)], ['101'])).
% 1.65/1.84  thf('103', plain,
% 1.65/1.84      ((![X0 : $i]:
% 1.65/1.84          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.65/1.84         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.65/1.84      inference('sup-', [status(thm)], ['100', '102'])).
% 1.65/1.84  thf('104', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X0)
% 1.65/1.84          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.65/1.84      inference('demod', [status(thm)], ['47', '48'])).
% 1.65/1.84  thf('105', plain,
% 1.65/1.84      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.65/1.84  thf('106', plain,
% 1.65/1.84      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 1.65/1.84         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.65/1.84      inference('split', [status(esa)], ['101'])).
% 1.65/1.84  thf('107', plain,
% 1.65/1.84      ((![X0 : $i]:
% 1.65/1.84          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.65/1.84         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.65/1.84      inference('sup-', [status(thm)], ['105', '106'])).
% 1.65/1.84  thf('108', plain,
% 1.65/1.84      (((((k1_xboole_0) != (k1_xboole_0))
% 1.65/1.84         | ~ (v1_relat_1 @ sk_A)
% 1.65/1.84         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.65/1.84         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.65/1.84      inference('sup-', [status(thm)], ['104', '107'])).
% 1.65/1.84  thf('109', plain, ((v1_relat_1 @ sk_A)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('110', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.84  thf('111', plain,
% 1.65/1.84      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.65/1.84         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.65/1.84      inference('demod', [status(thm)], ['108', '109', '110'])).
% 1.65/1.84  thf('112', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.65/1.84      inference('simplify', [status(thm)], ['111'])).
% 1.65/1.84  thf('113', plain,
% 1.65/1.84      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 1.65/1.84       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.65/1.84      inference('split', [status(esa)], ['101'])).
% 1.65/1.84  thf('114', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 1.65/1.84      inference('sat_resolution*', [status(thm)], ['112', '113'])).
% 1.65/1.84  thf('115', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.84      inference('simpl_trail', [status(thm)], ['103', '114'])).
% 1.65/1.84  thf('116', plain,
% 1.65/1.84      ((((k1_xboole_0) != (k1_xboole_0))
% 1.65/1.84        | ~ (v1_relat_1 @ sk_A)
% 1.65/1.84        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.65/1.84      inference('sup-', [status(thm)], ['99', '115'])).
% 1.65/1.84  thf('117', plain, ((v1_relat_1 @ sk_A)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('118', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.84  thf('119', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.65/1.84      inference('demod', [status(thm)], ['116', '117', '118'])).
% 1.65/1.84  thf('120', plain, ($false), inference('simplify', [status(thm)], ['119'])).
% 1.65/1.84  
% 1.65/1.84  % SZS output end Refutation
% 1.65/1.84  
% 1.65/1.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
