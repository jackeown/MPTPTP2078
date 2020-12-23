%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dkEMeqAin5

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:36 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 327 expanded)
%              Number of leaves         :   26 ( 110 expanded)
%              Depth                    :   33
%              Number of atoms          :  860 (2293 expanded)
%              Number of equality atoms :   97 ( 265 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('5',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,
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

thf('7',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X31 @ X30 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('10',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('15',plain,(
    ! [X28: $i] :
      ( ( ( k3_xboole_0 @ X28 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X28 ) @ ( k2_relat_1 @ X28 ) ) )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_zfmisc_1 @ X18 @ X19 )
        = k1_xboole_0 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('18',plain,(
    ! [X19: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('29',plain,
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

thf('30',plain,(
    ! [X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_zfmisc_1 @ X18 @ X19 )
        = k1_xboole_0 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,(
    ! [X18: $i] :
      ( ( k2_zfmisc_1 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X28: $i] :
      ( ( ( k3_xboole_0 @ X28 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X28 ) @ ( k2_relat_1 @ X28 ) ) )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,
    ( ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('48',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X33 @ X32 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X32 ) @ ( k4_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('52',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

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

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','25'])).

thf('57',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['63'])).

thf('65',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','64'])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('73',plain,(
    ! [X27: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X27 ) )
        = X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','76'])).

thf('78',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
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
    inference(demod,[status(thm)],['23','24'])).

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
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dkEMeqAin5
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:44:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.76/0.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.94  % Solved by: fo/fo7.sh
% 0.76/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.94  % done 1146 iterations in 0.491s
% 0.76/0.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.94  % SZS output start Refutation
% 0.76/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.94  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.76/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.94  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.94  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.76/0.94  thf(dt_k5_relat_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.76/0.94       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.76/0.94  thf('0', plain,
% 0.76/0.94      (![X24 : $i, X25 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ X24)
% 0.76/0.94          | ~ (v1_relat_1 @ X25)
% 0.76/0.94          | (v1_relat_1 @ (k5_relat_1 @ X24 @ X25)))),
% 0.76/0.94      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.76/0.94  thf(dt_k4_relat_1, axiom,
% 0.76/0.94    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.76/0.94  thf('1', plain,
% 0.76/0.94      (![X23 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X23)) | ~ (v1_relat_1 @ X23))),
% 0.76/0.94      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.76/0.94  thf(l13_xboole_0, axiom,
% 0.76/0.94    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.76/0.94  thf('2', plain,
% 0.76/0.94      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.76/0.94  thf(cc1_relat_1, axiom,
% 0.76/0.94    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.76/0.94  thf('3', plain, (![X22 : $i]: ((v1_relat_1 @ X22) | ~ (v1_xboole_0 @ X22))),
% 0.76/0.94      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.76/0.94  thf('4', plain,
% 0.76/0.94      (![X24 : $i, X25 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ X24)
% 0.76/0.94          | ~ (v1_relat_1 @ X25)
% 0.76/0.94          | (v1_relat_1 @ (k5_relat_1 @ X24 @ X25)))),
% 0.76/0.94      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.76/0.94  thf('5', plain, (![X22 : $i]: ((v1_relat_1 @ X22) | ~ (v1_xboole_0 @ X22))),
% 0.76/0.94      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.76/0.94  thf(t60_relat_1, axiom,
% 0.76/0.94    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.76/0.94     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.76/0.94  thf('6', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.94      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.76/0.94  thf(t46_relat_1, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( v1_relat_1 @ A ) =>
% 0.76/0.94       ( ![B:$i]:
% 0.76/0.94         ( ( v1_relat_1 @ B ) =>
% 0.76/0.94           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.76/0.94             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.76/0.94  thf('7', plain,
% 0.76/0.94      (![X30 : $i, X31 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ X30)
% 0.76/0.94          | ((k1_relat_1 @ (k5_relat_1 @ X31 @ X30)) = (k1_relat_1 @ X31))
% 0.76/0.94          | ~ (r1_tarski @ (k2_relat_1 @ X31) @ (k1_relat_1 @ X30))
% 0.76/0.94          | ~ (v1_relat_1 @ X31))),
% 0.76/0.94      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.76/0.94  thf('8', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.76/0.94          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.76/0.94          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.76/0.94              = (k1_relat_1 @ k1_xboole_0))
% 0.76/0.94          | ~ (v1_relat_1 @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.94  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.76/0.94  thf('9', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.76/0.94      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.76/0.94  thf('10', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.94      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.76/0.94  thf('11', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ k1_xboole_0)
% 0.76/0.94          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.76/0.94          | ~ (v1_relat_1 @ X0))),
% 0.76/0.94      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.76/0.94  thf('12', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['5', '11'])).
% 0.76/0.94  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.76/0.94  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.94  thf('14', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ X0)
% 0.76/0.94          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.76/0.94      inference('demod', [status(thm)], ['12', '13'])).
% 0.76/0.94  thf(t22_relat_1, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( v1_relat_1 @ A ) =>
% 0.76/0.94       ( ( k3_xboole_0 @
% 0.76/0.94           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.76/0.94         ( A ) ) ))).
% 0.76/0.94  thf('15', plain,
% 0.76/0.94      (![X28 : $i]:
% 0.76/0.94         (((k3_xboole_0 @ X28 @ 
% 0.76/0.94            (k2_zfmisc_1 @ (k1_relat_1 @ X28) @ (k2_relat_1 @ X28))) = (
% 0.76/0.94            X28))
% 0.76/0.94          | ~ (v1_relat_1 @ X28))),
% 0.76/0.94      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.76/0.94  thf('16', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.76/0.94            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.76/0.94             (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.76/0.94            = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['14', '15'])).
% 0.76/0.94  thf(t113_zfmisc_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.76/0.94       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.76/0.94  thf('17', plain,
% 0.76/0.94      (![X18 : $i, X19 : $i]:
% 0.76/0.94         (((k2_zfmisc_1 @ X18 @ X19) = (k1_xboole_0))
% 0.76/0.94          | ((X18) != (k1_xboole_0)))),
% 0.76/0.94      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.76/0.94  thf('18', plain,
% 0.76/0.94      (![X19 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 0.76/0.94      inference('simplify', [status(thm)], ['17'])).
% 0.76/0.94  thf(t2_boole, axiom,
% 0.76/0.94    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.76/0.94  thf('19', plain,
% 0.76/0.94      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.94      inference('cnf', [status(esa)], [t2_boole])).
% 0.76/0.94  thf('20', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.76/0.94      inference('demod', [status(thm)], ['16', '18', '19'])).
% 0.76/0.94  thf('21', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['4', '20'])).
% 0.76/0.94  thf('22', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.76/0.94          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.76/0.94          | ~ (v1_relat_1 @ X0))),
% 0.76/0.94      inference('simplify', [status(thm)], ['21'])).
% 0.76/0.94  thf('23', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['3', '22'])).
% 0.76/0.94  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.94  thf('25', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ X0)
% 0.76/0.94          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.76/0.94      inference('demod', [status(thm)], ['23', '24'])).
% 0.76/0.94  thf('26', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.76/0.94          | ~ (v1_xboole_0 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ X1))),
% 0.76/0.94      inference('sup+', [status(thm)], ['2', '25'])).
% 0.76/0.94  thf('27', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ X0)
% 0.76/0.94          | ~ (v1_xboole_0 @ X1)
% 0.76/0.94          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['1', '26'])).
% 0.76/0.94  thf('28', plain, (![X22 : $i]: ((v1_relat_1 @ X22) | ~ (v1_xboole_0 @ X22))),
% 0.76/0.94      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.76/0.94  thf('29', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.94      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.76/0.94  thf(t37_relat_1, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( v1_relat_1 @ A ) =>
% 0.76/0.94       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.76/0.94         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.76/0.94  thf('30', plain,
% 0.76/0.94      (![X29 : $i]:
% 0.76/0.94         (((k1_relat_1 @ X29) = (k2_relat_1 @ (k4_relat_1 @ X29)))
% 0.76/0.94          | ~ (v1_relat_1 @ X29))),
% 0.76/0.94      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.76/0.94  thf('31', plain,
% 0.76/0.94      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.76/0.94  thf('32', plain,
% 0.76/0.94      (![X18 : $i, X19 : $i]:
% 0.76/0.94         (((k2_zfmisc_1 @ X18 @ X19) = (k1_xboole_0))
% 0.76/0.94          | ((X19) != (k1_xboole_0)))),
% 0.76/0.94      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.76/0.94  thf('33', plain,
% 0.76/0.94      (![X18 : $i]: ((k2_zfmisc_1 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.94      inference('simplify', [status(thm)], ['32'])).
% 0.76/0.94  thf('34', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['31', '33'])).
% 0.76/0.94  thf('35', plain,
% 0.76/0.94      (![X28 : $i]:
% 0.76/0.94         (((k3_xboole_0 @ X28 @ 
% 0.76/0.94            (k2_zfmisc_1 @ (k1_relat_1 @ X28) @ (k2_relat_1 @ X28))) = (
% 0.76/0.94            X28))
% 0.76/0.94          | ~ (v1_relat_1 @ X28))),
% 0.76/0.94      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.76/0.94  thf('36', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.76/0.94          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.76/0.94          | ~ (v1_relat_1 @ X0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['34', '35'])).
% 0.76/0.94  thf('37', plain,
% 0.76/0.94      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.94      inference('cnf', [status(esa)], [t2_boole])).
% 0.76/0.94  thf('38', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k1_xboole_0) = (X0))
% 0.76/0.94          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.76/0.94          | ~ (v1_relat_1 @ X0))),
% 0.76/0.94      inference('demod', [status(thm)], ['36', '37'])).
% 0.76/0.94  thf('39', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.76/0.94          | ((k1_xboole_0) = (k4_relat_1 @ X0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['30', '38'])).
% 0.76/0.94  thf('40', plain,
% 0.76/0.94      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.76/0.94        | ((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 0.76/0.94        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 0.76/0.94        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['29', '39'])).
% 0.76/0.94  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.94  thf('42', plain,
% 0.76/0.94      ((((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 0.76/0.94        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 0.76/0.94        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.76/0.94      inference('demod', [status(thm)], ['40', '41'])).
% 0.76/0.94  thf('43', plain,
% 0.76/0.94      (![X23 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X23)) | ~ (v1_relat_1 @ X23))),
% 0.76/0.94      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.76/0.94  thf('44', plain,
% 0.76/0.94      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.76/0.94        | ((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0)))),
% 0.76/0.94      inference('clc', [status(thm)], ['42', '43'])).
% 0.76/0.94  thf('45', plain,
% 0.76/0.94      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.76/0.94        | ((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['28', '44'])).
% 0.76/0.94  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.94  thf('47', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 0.76/0.94      inference('demod', [status(thm)], ['45', '46'])).
% 0.76/0.94  thf(t54_relat_1, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( v1_relat_1 @ A ) =>
% 0.76/0.94       ( ![B:$i]:
% 0.76/0.94         ( ( v1_relat_1 @ B ) =>
% 0.76/0.94           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.76/0.94             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.76/0.94  thf('48', plain,
% 0.76/0.94      (![X32 : $i, X33 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ X32)
% 0.76/0.94          | ((k4_relat_1 @ (k5_relat_1 @ X33 @ X32))
% 0.76/0.94              = (k5_relat_1 @ (k4_relat_1 @ X32) @ (k4_relat_1 @ X33)))
% 0.76/0.94          | ~ (v1_relat_1 @ X33))),
% 0.76/0.94      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.76/0.94  thf('49', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.76/0.94            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['47', '48'])).
% 0.76/0.94  thf('50', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.94      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.76/0.94  thf('51', plain,
% 0.76/0.94      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.76/0.94  thf('52', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.94      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.76/0.94  thf('53', plain,
% 0.76/0.94      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['51', '52'])).
% 0.76/0.94  thf(t62_relat_1, conjecture,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( v1_relat_1 @ A ) =>
% 0.76/0.94       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.76/0.94         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.76/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.94    (~( ![A:$i]:
% 0.76/0.94        ( ( v1_relat_1 @ A ) =>
% 0.76/0.94          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.76/0.94            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.76/0.94    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.76/0.94  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('55', plain, (![X22 : $i]: ((v1_relat_1 @ X22) | ~ (v1_xboole_0 @ X22))),
% 0.76/0.94      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.76/0.94  thf('56', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.76/0.94          | ~ (v1_xboole_0 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ X1))),
% 0.76/0.94      inference('sup+', [status(thm)], ['2', '25'])).
% 0.76/0.94  thf('57', plain,
% 0.76/0.94      (![X24 : $i, X25 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ X24)
% 0.76/0.94          | ~ (v1_relat_1 @ X25)
% 0.76/0.94          | (v1_relat_1 @ (k5_relat_1 @ X24 @ X25)))),
% 0.76/0.94      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.76/0.94  thf('58', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((v1_relat_1 @ k1_xboole_0)
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ~ (v1_xboole_0 @ X1)
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ X1))),
% 0.76/0.94      inference('sup+', [status(thm)], ['56', '57'])).
% 0.76/0.94  thf('59', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ X1)
% 0.76/0.94          | ~ (v1_xboole_0 @ X1)
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | (v1_relat_1 @ k1_xboole_0))),
% 0.76/0.94      inference('simplify', [status(thm)], ['58'])).
% 0.76/0.94  thf('60', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (~ (v1_xboole_0 @ X0)
% 0.76/0.94          | (v1_relat_1 @ k1_xboole_0)
% 0.76/0.94          | ~ (v1_relat_1 @ X1)
% 0.76/0.94          | ~ (v1_xboole_0 @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['55', '59'])).
% 0.76/0.94  thf('61', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ X1)
% 0.76/0.94          | (v1_relat_1 @ k1_xboole_0)
% 0.76/0.94          | ~ (v1_xboole_0 @ X0))),
% 0.76/0.94      inference('simplify', [status(thm)], ['60'])).
% 0.76/0.94  thf('62', plain,
% 0.76/0.94      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['54', '61'])).
% 0.76/0.94  thf('63', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((v1_relat_1 @ (k2_relat_1 @ X0))
% 0.76/0.94          | ~ (v1_xboole_0 @ X0)
% 0.76/0.94          | ~ (v1_xboole_0 @ X1))),
% 0.76/0.94      inference('sup+', [status(thm)], ['53', '62'])).
% 0.76/0.94  thf('64', plain,
% 0.76/0.94      (![X0 : $i]: ((v1_relat_1 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.94      inference('condensation', [status(thm)], ['63'])).
% 0.76/0.94  thf('65', plain,
% 0.76/0.94      (((v1_relat_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['50', '64'])).
% 0.76/0.94  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.94  thf('67', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.76/0.94      inference('demod', [status(thm)], ['65', '66'])).
% 0.76/0.94  thf('68', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.76/0.94            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 0.76/0.94          | ~ (v1_relat_1 @ X0))),
% 0.76/0.94      inference('demod', [status(thm)], ['49', '67'])).
% 0.76/0.94  thf('69', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.76/0.94          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ X0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['27', '68'])).
% 0.76/0.94  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.94  thf('71', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ X0))),
% 0.76/0.94      inference('demod', [status(thm)], ['69', '70'])).
% 0.76/0.94  thf('72', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ X0)
% 0.76/0.94          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.76/0.94      inference('simplify', [status(thm)], ['71'])).
% 0.76/0.94  thf(involutiveness_k4_relat_1, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.76/0.94  thf('73', plain,
% 0.76/0.94      (![X27 : $i]:
% 0.76/0.94         (((k4_relat_1 @ (k4_relat_1 @ X27)) = (X27)) | ~ (v1_relat_1 @ X27))),
% 0.76/0.94      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.76/0.94  thf('74', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['72', '73'])).
% 0.76/0.94  thf('75', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 0.76/0.94      inference('demod', [status(thm)], ['45', '46'])).
% 0.76/0.94  thf('76', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.76/0.94      inference('demod', [status(thm)], ['74', '75'])).
% 0.76/0.94  thf('77', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ k1_xboole_0)
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['0', '76'])).
% 0.76/0.94  thf('78', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.76/0.94      inference('demod', [status(thm)], ['65', '66'])).
% 0.76/0.94  thf('79', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ X0)
% 0.76/0.94          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.76/0.94      inference('demod', [status(thm)], ['77', '78'])).
% 0.76/0.94  thf('80', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.76/0.94          | ~ (v1_relat_1 @ X0))),
% 0.76/0.94      inference('simplify', [status(thm)], ['79'])).
% 0.76/0.94  thf('81', plain,
% 0.76/0.94      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.76/0.94  thf('82', plain,
% 0.76/0.94      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.76/0.94        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('83', plain,
% 0.76/0.94      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.76/0.94         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['82'])).
% 0.76/0.94  thf('84', plain,
% 0.76/0.94      ((![X0 : $i]:
% 0.76/0.94          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.76/0.94         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['81', '83'])).
% 0.76/0.94  thf('85', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (v1_relat_1 @ X0)
% 0.76/0.94          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.76/0.94      inference('demod', [status(thm)], ['23', '24'])).
% 0.76/0.94  thf('86', plain,
% 0.76/0.94      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.76/0.94  thf('87', plain,
% 0.76/0.94      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.76/0.94         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['82'])).
% 0.76/0.94  thf('88', plain,
% 0.76/0.94      ((![X0 : $i]:
% 0.76/0.94          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.76/0.94         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['86', '87'])).
% 0.76/0.94  thf('89', plain,
% 0.76/0.94      (((((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.94         | ~ (v1_relat_1 @ sk_A)
% 0.76/0.94         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.76/0.94         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['85', '88'])).
% 0.76/0.94  thf('90', plain, ((v1_relat_1 @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.94  thf('92', plain,
% 0.76/0.94      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.76/0.94         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.76/0.94      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.76/0.94  thf('93', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.76/0.94      inference('simplify', [status(thm)], ['92'])).
% 0.76/0.94  thf('94', plain,
% 0.76/0.94      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.76/0.94       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.76/0.94      inference('split', [status(esa)], ['82'])).
% 0.76/0.94  thf('95', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.76/0.94      inference('sat_resolution*', [status(thm)], ['93', '94'])).
% 0.76/0.94  thf('96', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.94      inference('simpl_trail', [status(thm)], ['84', '95'])).
% 0.76/0.94  thf('97', plain,
% 0.76/0.94      ((((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.94        | ~ (v1_relat_1 @ sk_A)
% 0.76/0.94        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['80', '96'])).
% 0.76/0.94  thf('98', plain, ((v1_relat_1 @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('99', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.94  thf('100', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.76/0.94      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.76/0.94  thf('101', plain, ($false), inference('simplify', [status(thm)], ['100'])).
% 0.76/0.94  
% 0.76/0.94  % SZS output end Refutation
% 0.76/0.94  
% 0.76/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
