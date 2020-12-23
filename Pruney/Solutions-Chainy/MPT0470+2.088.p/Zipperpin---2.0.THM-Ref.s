%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ullr5wLvn8

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 165 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   19
%              Number of atoms          :  753 (1222 expanded)
%              Number of equality atoms :   85 ( 149 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X44: $i] :
      ( ( v1_relat_1 @ X44 )
      | ~ ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ~ ( v1_relat_1 @ X46 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X44: $i] :
      ( ( v1_relat_1 @ X44 )
      | ~ ( v1_xboole_0 @ X44 ) ) ),
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

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X50 @ X51 ) )
        = ( k2_relat_1 @ X51 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X50 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('12',plain,(
    ! [X47: $i] :
      ( ( ( k3_xboole_0 @ X47 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) ) )
        = X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('22',plain,(
    ! [X38: $i,X40: $i,X41: $i] :
      ( ( k2_zfmisc_1 @ X41 @ ( k4_xboole_0 @ X38 @ X40 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X41 @ X38 ) @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('25',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','26'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['13','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

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

thf('35',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
    ! [X44: $i] :
      ( ( v1_relat_1 @ X44 )
      | ~ ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('38',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ~ ( v1_relat_1 @ X46 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('39',plain,(
    ! [X44: $i] :
      ( ( v1_relat_1 @ X44 )
      | ~ ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('40',plain,
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

thf('41',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X49 @ X48 ) )
        = ( k1_relat_1 @ X49 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X49 ) @ ( k1_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X47: $i] :
      ( ( ( k3_xboole_0 @ X47 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) ) )
        = X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('53',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X38 @ X40 ) @ X39 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X38 @ X39 ) @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('56',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','57'])).

thf('59',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('67',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('72',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['36','72'])).

thf('74',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference(simplify,[status(thm)],['76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ullr5wLvn8
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:26:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 75 iterations in 0.037s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(cc1_relat_1, axiom,
% 0.22/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.22/0.50  thf('0', plain, (![X44 : $i]: ((v1_relat_1 @ X44) | ~ (v1_xboole_0 @ X44))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.22/0.50  thf(dt_k5_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.22/0.50       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X45 : $i, X46 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X45)
% 0.22/0.50          | ~ (v1_relat_1 @ X46)
% 0.22/0.50          | (v1_relat_1 @ (k5_relat_1 @ X45 @ X46)))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.22/0.50  thf('2', plain, (![X44 : $i]: ((v1_relat_1 @ X44) | ~ (v1_xboole_0 @ X44))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.22/0.50  thf(t60_relat_1, axiom,
% 0.22/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('3', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf(t47_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( v1_relat_1 @ B ) =>
% 0.22/0.50           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.22/0.50             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X50 : $i, X51 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X50)
% 0.22/0.50          | ((k2_relat_1 @ (k5_relat_1 @ X50 @ X51)) = (k2_relat_1 @ X51))
% 0.22/0.50          | ~ (r1_tarski @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X50))
% 0.22/0.50          | ~ (v1_relat_1 @ X51))),
% 0.22/0.50      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.50          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.50              = (k2_relat_1 @ k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.50  thf('6', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf('7', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.50          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '8'])).
% 0.22/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.50  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf(t22_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( k3_xboole_0 @
% 0.22/0.50           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.22/0.50         ( A ) ) ))).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X47 : $i]:
% 0.22/0.50         (((k3_xboole_0 @ X47 @ 
% 0.22/0.50            (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47))) = (
% 0.22/0.50            X47))
% 0.22/0.50          | ~ (v1_relat_1 @ X47))),
% 0.22/0.50      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k3_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.22/0.50            (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.22/0.50             k1_xboole_0))
% 0.22/0.50            = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf(t46_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.50  thf(t21_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]:
% 0.22/0.50         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.22/0.50  thf(t100_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X1 : $i, X2 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ X1 @ X2)
% 0.22/0.50           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.22/0.50           = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['14', '17'])).
% 0.22/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.50  thf('19', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X1 : $i, X2 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ X1 @ X2)
% 0.22/0.50           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf(t125_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.22/0.50         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.22/0.50       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.50         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X38 : $i, X40 : $i, X41 : $i]:
% 0.22/0.50         ((k2_zfmisc_1 @ X41 @ (k4_xboole_0 @ X38 @ X40))
% 0.22/0.50           = (k4_xboole_0 @ (k2_zfmisc_1 @ X41 @ X38) @ 
% 0.22/0.50              (k2_zfmisc_1 @ X41 @ X40)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.22/0.50           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['21', '22'])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf('25', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['14', '17'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['18', '26'])).
% 0.22/0.50  thf(t2_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['13', '27', '28'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '31'])).
% 0.22/0.50  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.50  thf(t62_relat_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.22/0.50         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( v1_relat_1 @ A ) =>
% 0.22/0.50          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.22/0.50            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.22/0.50        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.50         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['35'])).
% 0.22/0.50  thf('37', plain, (![X44 : $i]: ((v1_relat_1 @ X44) | ~ (v1_xboole_0 @ X44))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X45 : $i, X46 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X45)
% 0.22/0.50          | ~ (v1_relat_1 @ X46)
% 0.22/0.50          | (v1_relat_1 @ (k5_relat_1 @ X45 @ X46)))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.22/0.50  thf('39', plain, (![X44 : $i]: ((v1_relat_1 @ X44) | ~ (v1_xboole_0 @ X44))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.22/0.50  thf('40', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf(t46_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( v1_relat_1 @ B ) =>
% 0.22/0.50           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.50             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X48 : $i, X49 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X48)
% 0.22/0.50          | ((k1_relat_1 @ (k5_relat_1 @ X49 @ X48)) = (k1_relat_1 @ X49))
% 0.22/0.50          | ~ (r1_tarski @ (k2_relat_1 @ X49) @ (k1_relat_1 @ X48))
% 0.22/0.50          | ~ (v1_relat_1 @ X49))),
% 0.22/0.50      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.50          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.50              = (k1_relat_1 @ k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.50  thf('43', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf('44', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.50          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '45'])).
% 0.22/0.50  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      (![X47 : $i]:
% 0.22/0.50         (((k3_xboole_0 @ X47 @ 
% 0.22/0.50            (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47))) = (
% 0.22/0.50            X47))
% 0.22/0.50          | ~ (v1_relat_1 @ X47))),
% 0.22/0.50      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.22/0.50            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.22/0.50             (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.22/0.50            = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['48', '49'])).
% 0.22/0.50  thf('51', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['14', '17'])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf('53', plain,
% 0.22/0.50      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.22/0.50         ((k2_zfmisc_1 @ (k4_xboole_0 @ X38 @ X40) @ X39)
% 0.22/0.50           = (k4_xboole_0 @ (k2_zfmisc_1 @ X38 @ X39) @ 
% 0.22/0.50              (k2_zfmisc_1 @ X40 @ X39)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.22/0.50           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['52', '53'])).
% 0.22/0.50  thf('55', plain,
% 0.22/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf('56', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['14', '17'])).
% 0.22/0.50  thf('57', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['51', '57'])).
% 0.22/0.50  thf('59', plain,
% 0.22/0.50      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.50  thf('60', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['50', '58', '59'])).
% 0.22/0.50  thf('61', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['38', '60'])).
% 0.22/0.50  thf('62', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['61'])).
% 0.22/0.50  thf('63', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['37', '62'])).
% 0.22/0.50  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.50  thf('65', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['63', '64'])).
% 0.22/0.50  thf('66', plain,
% 0.22/0.50      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.22/0.50         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['35'])).
% 0.22/0.50  thf('67', plain,
% 0.22/0.50      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.22/0.50         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.50  thf('68', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('69', plain,
% 0.22/0.50      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.50         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['67', '68'])).
% 0.22/0.50  thf('70', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['69'])).
% 0.22/0.50  thf('71', plain,
% 0.22/0.50      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.22/0.50       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('split', [status(esa)], ['35'])).
% 0.22/0.50  thf('72', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.22/0.50  thf('73', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['36', '72'])).
% 0.22/0.50  thf('74', plain,
% 0.22/0.50      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['34', '73'])).
% 0.22/0.50  thf('75', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('76', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['74', '75'])).
% 0.22/0.50  thf('77', plain, ($false), inference('simplify', [status(thm)], ['76'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
