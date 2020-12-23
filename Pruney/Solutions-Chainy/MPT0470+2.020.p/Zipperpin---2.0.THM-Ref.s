%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i5o7LGHkww

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 702 expanded)
%              Number of leaves         :   31 ( 240 expanded)
%              Depth                    :   32
%              Number of atoms          :  757 (4647 expanded)
%              Number of equality atoms :   87 ( 576 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k6_subset_1 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X27 @ X26 ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X27 ) @ ( k4_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k6_subset_1 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ ( k6_subset_1 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','12'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('16',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_relat_1 @ ( k6_subset_1 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k4_relat_1 @ ( k6_subset_1 @ X0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['3','22'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','25'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X31 @ X30 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X30 ) @ ( k4_relat_1 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('31',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','25'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k6_subset_1 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('42',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('43',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X29 @ X28 ) ) @ ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','38'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('49',plain,(
    ! [X25: $i] :
      ( ( ( k3_xboole_0 @ X25 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X25 ) @ ( k2_relat_1 @ X25 ) ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('52',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('56',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','38'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','58'])).

thf('60',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('62',plain,(
    ! [X24: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X24 ) )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','25'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','65'])).

thf('67',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','38'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

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

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('73',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('74',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('79',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('80',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['71','79'])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference(simplify,[status(thm)],['83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i5o7LGHkww
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:42:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 288 iterations in 0.075s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(dt_k5_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.20/0.52       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X22)
% 0.20/0.52          | ~ (v1_relat_1 @ X23)
% 0.20/0.52          | (v1_relat_1 @ (k5_relat_1 @ X22 @ X23)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.52      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.52  thf(cc1_relat_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.20/0.52  thf('3', plain, (![X20 : $i]: ((v1_relat_1 @ X20) | ~ (v1_xboole_0 @ X20))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.52  thf(t3_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.52  thf('4', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.52  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]:
% 0.20/0.52         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.52  thf('6', plain, (![X5 : $i]: ((k6_subset_1 @ X5 @ k1_xboole_0) = (X5))),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf(t41_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( v1_relat_1 @ B ) =>
% 0.20/0.52           ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) ) =
% 0.20/0.52             ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X26)
% 0.20/0.52          | ((k4_relat_1 @ (k6_subset_1 @ X27 @ X26))
% 0.20/0.52              = (k6_subset_1 @ (k4_relat_1 @ X27) @ (k4_relat_1 @ X26)))
% 0.20/0.52          | ~ (v1_relat_1 @ X27))),
% 0.20/0.52      inference('cnf', [status(esa)], [t41_relat_1])).
% 0.20/0.52  thf('8', plain, (![X5 : $i]: ((k6_subset_1 @ X5 @ k1_xboole_0) = (X5))),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf(t48_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.20/0.52           = (k3_xboole_0 @ X6 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]:
% 0.20/0.52         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]:
% 0.20/0.52         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         ((k6_subset_1 @ X6 @ (k6_subset_1 @ X6 @ X7))
% 0.20/0.52           = (k3_xboole_0 @ X6 @ X7))),
% 0.20/0.52      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['8', '12'])).
% 0.20/0.52  thf(t2_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.52  thf('15', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.52  thf('16', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i, X2 : $i]:
% 0.20/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X1 @ (k6_subset_1 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X1 @ (k4_relat_1 @ (k6_subset_1 @ X0 @ X0)))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((X1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X1) = (k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ (k4_relat_1 @ (k6_subset_1 @ X0 @ X0))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X0 @ (k4_relat_1 @ k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.53          | ((X0) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.53          | ((X0) = (k1_xboole_0))
% 0.20/0.53          | ~ (r1_tarski @ X0 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '22'])).
% 0.20/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.53  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((X0) = (k1_xboole_0))
% 0.20/0.53          | ~ (r1_tarski @ X0 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '25'])).
% 0.20/0.53  thf(t54_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( v1_relat_1 @ B ) =>
% 0.20/0.53           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.53             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X30)
% 0.20/0.53          | ((k4_relat_1 @ (k5_relat_1 @ X31 @ X30))
% 0.20/0.53              = (k5_relat_1 @ (k4_relat_1 @ X30) @ (k4_relat_1 @ X31)))
% 0.20/0.53          | ~ (v1_relat_1 @ X31))),
% 0.20/0.53      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.53            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain, (![X20 : $i]: ((v1_relat_1 @ X20) | ~ (v1_xboole_0 @ X20))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.53  thf('30', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('31', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '25'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i]: ((k4_relat_1 @ (k6_subset_1 @ X0 @ X0)) = (k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf(dt_k4_relat_1, axiom,
% 0.20/0.53    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X21 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X21)) | ~ (v1_relat_1 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ (k6_subset_1 @ X0 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (k6_subset_1 @ X0 @ X0))
% 0.20/0.53          | (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['29', '34'])).
% 0.20/0.53  thf('36', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.53  thf('38', plain, (![X0 : $i]: (v1_xboole_0 @ (k6_subset_1 @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['35', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.53            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X22)
% 0.20/0.53          | ~ (v1_relat_1 @ X23)
% 0.20/0.53          | (v1_relat_1 @ (k5_relat_1 @ X22 @ X23)))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.53  thf(t60_relat_1, axiom,
% 0.20/0.53    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.53     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('42', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.53  thf(t44_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( v1_relat_1 @ B ) =>
% 0.20/0.53           ( r1_tarski @
% 0.20/0.53             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X28 : $i, X29 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X28)
% 0.20/0.53          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X29 @ X28)) @ 
% 0.20/0.53             (k1_relat_1 @ X29))
% 0.20/0.53          | ~ (v1_relat_1 @ X29))),
% 0.20/0.53      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.20/0.53           k1_xboole_0)
% 0.20/0.53          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['35', '38'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.20/0.53           k1_xboole_0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf(t22_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ( k3_xboole_0 @
% 0.20/0.53           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.20/0.53         ( A ) ) ))).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X25 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X25 @ 
% 0.20/0.53            (k2_zfmisc_1 @ (k1_relat_1 @ X25) @ (k2_relat_1 @ X25))) = (
% 0.20/0.53            X25))
% 0.20/0.53          | ~ (v1_relat_1 @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.20/0.53            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.20/0.53             (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.20/0.53            = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['48', '49'])).
% 0.20/0.53  thf(t113_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i]:
% 0.20/0.53         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 0.20/0.53          | ((X14) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X15 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['50', '52', '53'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['41', '54'])).
% 0.20/0.53  thf('56', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['35', '38'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['57'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['40', '58'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X21 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X21)) | ~ (v1_relat_1 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 0.20/0.53      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.53  thf(involutiveness_k4_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (![X24 : $i]:
% 0.20/0.53         (((k4_relat_1 @ (k4_relat_1 @ X24)) = (X24)) | ~ (v1_relat_1 @ X24))),
% 0.20/0.53      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['61', '62'])).
% 0.20/0.53  thf('64', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '25'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '65'])).
% 0.20/0.53  thf('67', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['35', '38'])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.53  thf(t62_relat_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.20/0.53         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( v1_relat_1 @ A ) =>
% 0.20/0.53          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.20/0.53            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.20/0.53        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.53         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['70'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['57'])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.20/0.53         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['70'])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.20/0.53         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf('75', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.53         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('77', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['76'])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.20/0.53       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('split', [status(esa)], ['70'])).
% 0.20/0.53  thf('79', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 0.20/0.53  thf('80', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['71', '79'])).
% 0.20/0.53  thf('81', plain,
% 0.20/0.53      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['69', '80'])).
% 0.20/0.53  thf('82', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('83', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['81', '82'])).
% 0.20/0.53  thf('84', plain, ($false), inference('simplify', [status(thm)], ['83'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
