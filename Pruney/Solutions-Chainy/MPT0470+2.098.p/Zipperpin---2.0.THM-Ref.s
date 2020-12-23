%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0lgMHIwMhH

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:40 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 643 expanded)
%              Number of leaves         :   28 ( 207 expanded)
%              Depth                    :   21
%              Number of atoms          :  756 (4765 expanded)
%              Number of equality atoms :   72 ( 456 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('14',plain,(
    ! [X20: $i] :
      ( ( ( k3_xboole_0 @ X20 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['15','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('25',plain,(
    ! [X19: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X23 ) @ ( k4_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','29'])).

thf('31',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('45',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('46',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('48',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('49',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('50',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X23 ) @ ( k4_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('51',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('59',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('63',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','61','62'])).

thf('64',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','61','62'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','63','64'])).

thf('66',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('69',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['66'])).

thf('70',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['66'])).

thf('75',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['73','74'])).

thf('76',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['67','75'])).

thf('77',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(simplify,[status(thm)],['79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0lgMHIwMhH
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 09:29:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 609 iterations in 0.331s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.58/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.58/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.77  thf(dt_k5_relat_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.58/0.77       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.58/0.77  thf('0', plain,
% 0.58/0.77      (![X17 : $i, X18 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X17)
% 0.58/0.77          | ~ (v1_relat_1 @ X18)
% 0.58/0.77          | (v1_relat_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.58/0.77  thf(t60_relat_1, axiom,
% 0.58/0.77    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.58/0.77     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.58/0.77  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.77      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.77  thf(t45_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( v1_relat_1 @ B ) =>
% 0.58/0.77           ( r1_tarski @
% 0.58/0.77             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.58/0.77  thf('2', plain,
% 0.58/0.77      (![X21 : $i, X22 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X21)
% 0.58/0.77          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X22 @ X21)) @ 
% 0.58/0.77             (k2_relat_1 @ X21))
% 0.58/0.77          | ~ (v1_relat_1 @ X22))),
% 0.58/0.77      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.58/0.77  thf('3', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.58/0.77           k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['1', '2'])).
% 0.58/0.77  thf(t62_relat_1, conjecture,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) =>
% 0.58/0.77       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.58/0.77         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i]:
% 0.58/0.77        ( ( v1_relat_1 @ A ) =>
% 0.58/0.77          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.58/0.77            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.58/0.77  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(t4_subset_1, axiom,
% 0.58/0.77    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.58/0.77  thf('5', plain,
% 0.58/0.77      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.58/0.77      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.58/0.77  thf(cc2_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.58/0.77  thf('6', plain,
% 0.58/0.77      (![X14 : $i, X15 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.58/0.77          | (v1_relat_1 @ X14)
% 0.58/0.77          | ~ (v1_relat_1 @ X15))),
% 0.58/0.77      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.58/0.77  thf('7', plain,
% 0.58/0.77      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.77  thf('8', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.58/0.77      inference('sup-', [status(thm)], ['4', '7'])).
% 0.58/0.77  thf('9', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.58/0.77           k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['3', '8'])).
% 0.58/0.77  thf(l32_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.77  thf('10', plain,
% 0.58/0.77      (![X0 : $i, X2 : $i]:
% 0.58/0.77         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.58/0.77      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ((k4_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.58/0.77              k1_xboole_0) = (k1_xboole_0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['9', '10'])).
% 0.58/0.77  thf(t3_boole, axiom,
% 0.58/0.77    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.77  thf('12', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.58/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.77  thf('13', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['11', '12'])).
% 0.58/0.77  thf(t22_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) =>
% 0.58/0.77       ( ( k3_xboole_0 @
% 0.58/0.77           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.58/0.77         ( A ) ) ))).
% 0.58/0.77  thf('14', plain,
% 0.58/0.77      (![X20 : $i]:
% 0.58/0.77         (((k3_xboole_0 @ X20 @ 
% 0.58/0.77            (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20))) = (
% 0.58/0.77            X20))
% 0.58/0.77          | ~ (v1_relat_1 @ X20))),
% 0.58/0.77      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.58/0.77  thf('15', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k3_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.58/0.77            (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.58/0.77             k1_xboole_0))
% 0.58/0.77            = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['13', '14'])).
% 0.58/0.77  thf(t113_zfmisc_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.58/0.77       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.77  thf('16', plain,
% 0.58/0.77      (![X8 : $i, X9 : $i]:
% 0.58/0.77         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.58/0.77      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.58/0.77  thf('17', plain,
% 0.58/0.77      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['16'])).
% 0.58/0.77  thf(t2_boole, axiom,
% 0.58/0.77    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.58/0.77  thf('18', plain,
% 0.58/0.77      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.77      inference('cnf', [status(esa)], [t2_boole])).
% 0.58/0.77  thf('19', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['15', '17', '18'])).
% 0.58/0.77  thf('20', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['0', '19'])).
% 0.58/0.77  thf('21', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.58/0.77      inference('sup-', [status(thm)], ['4', '7'])).
% 0.58/0.77  thf('22', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('23', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['22'])).
% 0.58/0.77  thf(dt_k4_relat_1, axiom,
% 0.58/0.77    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.58/0.77  thf('24', plain,
% 0.58/0.77      (![X16 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X16)) | ~ (v1_relat_1 @ X16))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.58/0.77  thf(involutiveness_k4_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.58/0.77  thf('25', plain,
% 0.58/0.77      (![X19 : $i]:
% 0.58/0.77         (((k4_relat_1 @ (k4_relat_1 @ X19)) = (X19)) | ~ (v1_relat_1 @ X19))),
% 0.58/0.77      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.58/0.77  thf(t54_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( v1_relat_1 @ B ) =>
% 0.58/0.77           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.58/0.77             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.58/0.77  thf('26', plain,
% 0.58/0.77      (![X23 : $i, X24 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X23)
% 0.58/0.77          | ((k4_relat_1 @ (k5_relat_1 @ X24 @ X23))
% 0.58/0.77              = (k5_relat_1 @ (k4_relat_1 @ X23) @ (k4_relat_1 @ X24)))
% 0.58/0.77          | ~ (v1_relat_1 @ X24))),
% 0.58/0.77      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.58/0.77  thf('27', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 0.58/0.77            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['25', '26'])).
% 0.58/0.77  thf('28', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X1)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 0.58/0.77              = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['24', '27'])).
% 0.58/0.77  thf('29', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 0.58/0.77            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ X1)
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['28'])).
% 0.58/0.77  thf('30', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k4_relat_1 @ k1_xboole_0)
% 0.58/0.77            = (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['23', '29'])).
% 0.58/0.77  thf('31', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.58/0.77      inference('sup-', [status(thm)], ['4', '7'])).
% 0.58/0.77  thf('32', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k4_relat_1 @ k1_xboole_0)
% 0.58/0.77            = (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['30', '31'])).
% 0.58/0.77  thf('33', plain,
% 0.58/0.77      (![X16 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X16)) | ~ (v1_relat_1 @ X16))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.58/0.77  thf('34', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ((k4_relat_1 @ k1_xboole_0)
% 0.58/0.77              = (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ X0)))),
% 0.58/0.77      inference('clc', [status(thm)], ['32', '33'])).
% 0.58/0.77  thf('35', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.58/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.77  thf(t48_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.77  thf('36', plain,
% 0.58/0.77      (![X5 : $i, X6 : $i]:
% 0.58/0.77         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.58/0.77           = (k3_xboole_0 @ X5 @ X6))),
% 0.58/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.77  thf('37', plain,
% 0.58/0.77      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['35', '36'])).
% 0.58/0.77  thf('38', plain,
% 0.58/0.77      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.77      inference('cnf', [status(esa)], [t2_boole])).
% 0.58/0.77  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.77      inference('demod', [status(thm)], ['37', '38'])).
% 0.58/0.77  thf('40', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['22'])).
% 0.58/0.77  thf('41', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((k1_xboole_0) = (k5_relat_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)))
% 0.58/0.77          | ~ (v1_relat_1 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['39', '40'])).
% 0.58/0.77  thf('42', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ((k4_relat_1 @ k1_xboole_0)
% 0.58/0.77              = (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ X0)))),
% 0.58/0.77      inference('clc', [status(thm)], ['32', '33'])).
% 0.58/0.77  thf('43', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['41', '42'])).
% 0.58/0.77  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.77      inference('demod', [status(thm)], ['37', '38'])).
% 0.58/0.77  thf('45', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.58/0.77      inference('sup-', [status(thm)], ['4', '7'])).
% 0.58/0.77  thf('46', plain, (![X0 : $i]: (v1_relat_1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['44', '45'])).
% 0.58/0.77  thf('47', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((k1_xboole_0) = (k5_relat_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)))
% 0.58/0.77          | ~ (v1_relat_1 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['39', '40'])).
% 0.58/0.77  thf('48', plain,
% 0.58/0.77      (![X16 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X16)) | ~ (v1_relat_1 @ X16))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.58/0.77  thf('49', plain,
% 0.58/0.77      (![X16 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X16)) | ~ (v1_relat_1 @ X16))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.58/0.77  thf('50', plain,
% 0.58/0.77      (![X23 : $i, X24 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X23)
% 0.58/0.77          | ((k4_relat_1 @ (k5_relat_1 @ X24 @ X23))
% 0.58/0.77              = (k5_relat_1 @ (k4_relat_1 @ X23) @ (k4_relat_1 @ X24)))
% 0.58/0.77          | ~ (v1_relat_1 @ X24))),
% 0.58/0.77      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.58/0.77  thf('51', plain,
% 0.58/0.77      (![X17 : $i, X18 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X17)
% 0.58/0.77          | ~ (v1_relat_1 @ X18)
% 0.58/0.77          | (v1_relat_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.58/0.77  thf('52', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.58/0.77          | ~ (v1_relat_1 @ X1)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 0.58/0.77          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['50', '51'])).
% 0.58/0.77  thf('53', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 0.58/0.77          | ~ (v1_relat_1 @ X1)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['49', '52'])).
% 0.58/0.77  thf('54', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.58/0.77          | ~ (v1_relat_1 @ X1)
% 0.58/0.77          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['53'])).
% 0.58/0.77  thf('55', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X1)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['48', '54'])).
% 0.58/0.77  thf('56', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.58/0.77          | ~ (v1_relat_1 @ X1)
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['55'])).
% 0.58/0.77  thf('57', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 0.58/0.77          | ~ (v1_relat_1 @ X1)
% 0.58/0.77          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['47', '56'])).
% 0.58/0.77  thf('58', plain, (![X0 : $i]: (v1_relat_1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['44', '45'])).
% 0.58/0.77  thf('59', plain,
% 0.58/0.77      (![X1 : $i]:
% 0.58/0.77         ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 0.58/0.77          | ~ (v1_relat_1 @ X1)
% 0.58/0.77          | ~ (v1_relat_1 @ X1))),
% 0.58/0.77      inference('demod', [status(thm)], ['57', '58'])).
% 0.58/0.77  thf('60', plain,
% 0.58/0.77      (![X1 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['59'])).
% 0.58/0.77  thf('61', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['46', '60'])).
% 0.58/0.77  thf('62', plain, (![X0 : $i]: (v1_relat_1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['44', '45'])).
% 0.58/0.77  thf('63', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.77      inference('demod', [status(thm)], ['43', '61', '62'])).
% 0.58/0.77  thf('64', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.77      inference('demod', [status(thm)], ['43', '61', '62'])).
% 0.58/0.77  thf('65', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['34', '63', '64'])).
% 0.58/0.77  thf('66', plain,
% 0.58/0.77      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.58/0.77        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('67', plain,
% 0.58/0.77      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.58/0.77         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('split', [status(esa)], ['66'])).
% 0.58/0.77  thf('68', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['22'])).
% 0.58/0.77  thf('69', plain,
% 0.58/0.77      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.58/0.77         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.58/0.77      inference('split', [status(esa)], ['66'])).
% 0.58/0.77  thf('70', plain,
% 0.58/0.77      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.58/0.77         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['68', '69'])).
% 0.58/0.77  thf('71', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('72', plain,
% 0.58/0.77      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.58/0.77         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.58/0.77      inference('demod', [status(thm)], ['70', '71'])).
% 0.58/0.77  thf('73', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['72'])).
% 0.58/0.77  thf('74', plain,
% 0.58/0.77      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 0.58/0.77       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.58/0.77      inference('split', [status(esa)], ['66'])).
% 0.58/0.77  thf('75', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.58/0.77      inference('sat_resolution*', [status(thm)], ['73', '74'])).
% 0.58/0.77  thf('76', plain, (((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.58/0.77      inference('simpl_trail', [status(thm)], ['67', '75'])).
% 0.58/0.77  thf('77', plain,
% 0.58/0.77      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['65', '76'])).
% 0.58/0.77  thf('78', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('79', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.58/0.77      inference('demod', [status(thm)], ['77', '78'])).
% 0.58/0.77  thf('80', plain, ($false), inference('simplify', [status(thm)], ['79'])).
% 0.58/0.77  
% 0.58/0.77  % SZS output end Refutation
% 0.58/0.77  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
