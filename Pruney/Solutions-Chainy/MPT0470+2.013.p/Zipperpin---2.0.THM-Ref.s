%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CuWOAVyOz3

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:27 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 579 expanded)
%              Number of leaves         :   37 ( 196 expanded)
%              Depth                    :   28
%              Number of atoms          : 1098 (4100 expanded)
%              Number of equality atoms :  118 ( 490 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ~ ( v1_relat_1 @ X46 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

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

thf('1',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','11'])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X50 @ X49 ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X50 ) @ ( k4_relat_1 @ X49 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X50 @ X49 ) )
        = ( k4_xboole_0 @ ( k4_relat_1 @ X50 ) @ ( k4_relat_1 @ X49 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('18',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('19',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','26'])).

thf('28',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','27'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X54 @ X53 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X53 ) @ ( k4_relat_1 @ X54 ) ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X44: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X44 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('31',plain,(
    ! [X43: $i] :
      ( ( v1_relat_1 @ X43 )
      | ~ ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('32',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ~ ( v1_relat_1 @ X46 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('33',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('34',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('36',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X52 @ X51 ) ) @ ( k1_relat_1 @ X52 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('37',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('45',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('47',plain,(
    ! [X48: $i] :
      ( ( ( k3_xboole_0 @ X48 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) ) )
        = X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('48',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('49',plain,(
    ! [X48: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X48 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) ) ) )
        = X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('51',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('52',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('53',plain,(
    ! [X7: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','64'])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('71',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('73',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','27'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X44: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X44 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X43: $i] :
      ( ( v1_relat_1 @ X43 )
      | ~ ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66','79'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('81',plain,(
    ! [X47: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X47 ) )
        = X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','27'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','84'])).

thf('86',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','78'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('90',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ~ ( v1_relat_1 @ X46 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('94',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('95',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X52 @ X51 ) ) @ ( k1_relat_1 @ X52 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','78'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','104'])).

thf('106',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','78'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('110',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['90'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('115',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['90'])).

thf('118',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['92','118'])).

thf('120',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('123',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    $false ),
    inference(simplify,[status(thm)],['123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CuWOAVyOz3
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.69/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.89  % Solved by: fo/fo7.sh
% 0.69/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.89  % done 712 iterations in 0.430s
% 0.69/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.89  % SZS output start Refutation
% 0.69/0.89  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.69/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.89  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.69/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.89  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.69/0.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.69/0.89  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.69/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.89  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.69/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.89  thf(dt_k5_relat_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.69/0.89       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.69/0.89  thf('0', plain,
% 0.69/0.89      (![X45 : $i, X46 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X45)
% 0.69/0.89          | ~ (v1_relat_1 @ X46)
% 0.69/0.89          | (v1_relat_1 @ (k5_relat_1 @ X45 @ X46)))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.69/0.89  thf(t62_relat_1, conjecture,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) =>
% 0.69/0.89       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.69/0.89         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.69/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.89    (~( ![A:$i]:
% 0.69/0.89        ( ( v1_relat_1 @ A ) =>
% 0.69/0.89          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.69/0.89            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.69/0.89    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.69/0.89  thf('1', plain, ((v1_relat_1 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(d10_xboole_0, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.69/0.89  thf('2', plain,
% 0.69/0.89      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.69/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.89  thf('3', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.69/0.89      inference('simplify', [status(thm)], ['2'])).
% 0.69/0.89  thf(t92_xboole_1, axiom,
% 0.69/0.89    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.69/0.89  thf('4', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.69/0.89  thf(idempotence_k3_xboole_0, axiom,
% 0.69/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.69/0.89  thf('5', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.69/0.89      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.69/0.89  thf(t12_setfam_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.69/0.89  thf('6', plain,
% 0.69/0.89      (![X41 : $i, X42 : $i]:
% 0.69/0.89         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.69/0.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.69/0.89  thf('7', plain, (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['5', '6'])).
% 0.69/0.89  thf(t100_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.69/0.89  thf('8', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X5 @ X6)
% 0.69/0.89           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.69/0.89  thf('9', plain,
% 0.69/0.89      (![X41 : $i, X42 : $i]:
% 0.69/0.89         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.69/0.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.69/0.89  thf('10', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X5 @ X6)
% 0.69/0.89           = (k5_xboole_0 @ X5 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6))))),
% 0.69/0.89      inference('demod', [status(thm)], ['8', '9'])).
% 0.69/0.89  thf('11', plain,
% 0.69/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['7', '10'])).
% 0.69/0.89  thf('12', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['4', '11'])).
% 0.69/0.89  thf(t41_relat_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( v1_relat_1 @ B ) =>
% 0.69/0.89           ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) ) =
% 0.69/0.89             ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) ))).
% 0.69/0.89  thf('13', plain,
% 0.69/0.89      (![X49 : $i, X50 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X49)
% 0.69/0.89          | ((k4_relat_1 @ (k6_subset_1 @ X50 @ X49))
% 0.69/0.89              = (k6_subset_1 @ (k4_relat_1 @ X50) @ (k4_relat_1 @ X49)))
% 0.69/0.89          | ~ (v1_relat_1 @ X50))),
% 0.69/0.89      inference('cnf', [status(esa)], [t41_relat_1])).
% 0.69/0.89  thf(redefinition_k6_subset_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.69/0.89  thf('14', plain,
% 0.69/0.89      (![X39 : $i, X40 : $i]:
% 0.69/0.89         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.69/0.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.69/0.89  thf('15', plain,
% 0.69/0.89      (![X39 : $i, X40 : $i]:
% 0.69/0.89         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.69/0.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.69/0.89  thf('16', plain,
% 0.69/0.89      (![X49 : $i, X50 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X49)
% 0.69/0.89          | ((k4_relat_1 @ (k4_xboole_0 @ X50 @ X49))
% 0.69/0.89              = (k4_xboole_0 @ (k4_relat_1 @ X50) @ (k4_relat_1 @ X49)))
% 0.69/0.89          | ~ (v1_relat_1 @ X50))),
% 0.69/0.89      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.69/0.89  thf('17', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.69/0.89  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.69/0.89  thf('18', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.69/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.69/0.89  thf('19', plain,
% 0.69/0.89      (![X2 : $i, X4 : $i]:
% 0.69/0.89         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.69/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.89  thf('20', plain,
% 0.69/0.89      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['18', '19'])).
% 0.69/0.89  thf('21', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['17', '20'])).
% 0.69/0.89  thf('22', plain,
% 0.69/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['7', '10'])).
% 0.69/0.89  thf('23', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.69/0.89      inference('demod', [status(thm)], ['21', '22'])).
% 0.69/0.89  thf('24', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (r1_tarski @ X1 @ (k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)))
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ((X1) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['16', '23'])).
% 0.69/0.89  thf('25', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (((X1) = (k1_xboole_0))
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (r1_tarski @ X1 @ (k4_relat_1 @ (k4_xboole_0 @ X0 @ X0))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['24'])).
% 0.69/0.89  thf('26', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (r1_tarski @ X1 @ (k4_relat_1 @ k1_xboole_0))
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ((X1) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['12', '25'])).
% 0.69/0.89  thf('27', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['3', '26'])).
% 0.69/0.89  thf('28', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['1', '27'])).
% 0.69/0.89  thf(t54_relat_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( v1_relat_1 @ B ) =>
% 0.69/0.89           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.69/0.89             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.69/0.89  thf('29', plain,
% 0.69/0.89      (![X53 : $i, X54 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X53)
% 0.69/0.89          | ((k4_relat_1 @ (k5_relat_1 @ X54 @ X53))
% 0.69/0.89              = (k5_relat_1 @ (k4_relat_1 @ X53) @ (k4_relat_1 @ X54)))
% 0.69/0.89          | ~ (v1_relat_1 @ X54))),
% 0.69/0.89      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.69/0.89  thf(dt_k4_relat_1, axiom,
% 0.69/0.89    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.69/0.89  thf('30', plain,
% 0.69/0.89      (![X44 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X44)) | ~ (v1_relat_1 @ X44))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.69/0.89  thf(cc1_relat_1, axiom,
% 0.69/0.89    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.69/0.89  thf('31', plain, (![X43 : $i]: ((v1_relat_1 @ X43) | ~ (v1_xboole_0 @ X43))),
% 0.69/0.89      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.69/0.89  thf('32', plain,
% 0.69/0.89      (![X45 : $i, X46 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X45)
% 0.69/0.89          | ~ (v1_relat_1 @ X46)
% 0.69/0.89          | (v1_relat_1 @ (k5_relat_1 @ X45 @ X46)))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.69/0.89  thf(l13_xboole_0, axiom,
% 0.69/0.89    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.69/0.89  thf('33', plain,
% 0.69/0.89      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.89  thf(t60_relat_1, axiom,
% 0.69/0.89    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.69/0.89     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.69/0.89  thf('34', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.69/0.89  thf('35', plain,
% 0.69/0.89      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['33', '34'])).
% 0.69/0.89  thf(t44_relat_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( v1_relat_1 @ B ) =>
% 0.69/0.89           ( r1_tarski @
% 0.69/0.89             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.69/0.89  thf('36', plain,
% 0.69/0.89      (![X51 : $i, X52 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X51)
% 0.69/0.89          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X52 @ X51)) @ 
% 0.69/0.89             (k1_relat_1 @ X52))
% 0.69/0.89          | ~ (v1_relat_1 @ X52))),
% 0.69/0.89      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.69/0.89  thf('37', plain,
% 0.69/0.89      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.89  thf('38', plain,
% 0.69/0.89      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['18', '19'])).
% 0.69/0.89  thf('39', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (r1_tarski @ X1 @ X0)
% 0.69/0.89          | ~ (v1_xboole_0 @ X0)
% 0.69/0.89          | ((X1) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['37', '38'])).
% 0.69/0.89  thf('40', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ X1)
% 0.69/0.89          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ X1)) = (k1_xboole_0))
% 0.69/0.89          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['36', '39'])).
% 0.69/0.89  thf('41', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.89          | ~ (v1_xboole_0 @ X0)
% 0.69/0.89          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ X1)) = (k1_xboole_0))
% 0.69/0.89          | ~ (v1_relat_1 @ X1)
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['35', '40'])).
% 0.69/0.89  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.69/0.89  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.89  thf('43', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (v1_xboole_0 @ X0)
% 0.69/0.89          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ X1)) = (k1_xboole_0))
% 0.69/0.89          | ~ (v1_relat_1 @ X1)
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['41', '42'])).
% 0.69/0.89  thf(fc4_zfmisc_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.69/0.89  thf('44', plain,
% 0.69/0.89      (![X37 : $i, X38 : $i]:
% 0.69/0.89         (~ (v1_xboole_0 @ X37) | (v1_xboole_0 @ (k2_zfmisc_1 @ X37 @ X38)))),
% 0.69/0.89      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.69/0.89  thf('45', plain,
% 0.69/0.89      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.89  thf('46', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['44', '45'])).
% 0.69/0.89  thf(t22_relat_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) =>
% 0.69/0.89       ( ( k3_xboole_0 @
% 0.69/0.89           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.69/0.89         ( A ) ) ))).
% 0.69/0.89  thf('47', plain,
% 0.69/0.89      (![X48 : $i]:
% 0.69/0.89         (((k3_xboole_0 @ X48 @ 
% 0.69/0.89            (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))) = (
% 0.69/0.89            X48))
% 0.69/0.89          | ~ (v1_relat_1 @ X48))),
% 0.69/0.89      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.69/0.89  thf('48', plain,
% 0.69/0.89      (![X41 : $i, X42 : $i]:
% 0.69/0.89         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.69/0.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.69/0.89  thf('49', plain,
% 0.69/0.89      (![X48 : $i]:
% 0.69/0.89         (((k1_setfam_1 @ 
% 0.69/0.89            (k2_tarski @ X48 @ 
% 0.69/0.89             (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))))
% 0.69/0.89            = (X48))
% 0.69/0.89          | ~ (v1_relat_1 @ X48))),
% 0.69/0.89      inference('demod', [status(thm)], ['47', '48'])).
% 0.69/0.89  thf('50', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (X0))
% 0.69/0.89          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['46', '49'])).
% 0.69/0.89  thf(t2_boole, axiom,
% 0.69/0.89    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.69/0.89  thf('51', plain,
% 0.69/0.89      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [t2_boole])).
% 0.69/0.89  thf('52', plain,
% 0.69/0.89      (![X41 : $i, X42 : $i]:
% 0.69/0.89         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.69/0.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.69/0.89  thf('53', plain,
% 0.69/0.89      (![X7 : $i]:
% 0.69/0.89         ((k1_setfam_1 @ (k2_tarski @ X7 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['51', '52'])).
% 0.69/0.89  thf('54', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k1_xboole_0) = (X0))
% 0.69/0.89          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['50', '53'])).
% 0.69/0.89  thf('55', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.89          | ~ (v1_relat_1 @ X1)
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_xboole_0 @ X1)
% 0.69/0.89          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.69/0.89          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['43', '54'])).
% 0.69/0.89  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.89  thf('57', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X1)
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_xboole_0 @ X1)
% 0.69/0.89          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.69/0.89          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X0)))),
% 0.69/0.89      inference('demod', [status(thm)], ['55', '56'])).
% 0.69/0.89  thf('58', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ X1)
% 0.69/0.89          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 0.69/0.89          | ~ (v1_xboole_0 @ X1)
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ X1))),
% 0.69/0.89      inference('sup-', [status(thm)], ['32', '57'])).
% 0.69/0.89  thf('59', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (v1_xboole_0 @ X1)
% 0.69/0.89          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 0.69/0.89          | ~ (v1_relat_1 @ X1)
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('simplify', [status(thm)], ['58'])).
% 0.69/0.89  thf('60', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (v1_xboole_0 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ X1)
% 0.69/0.89          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.69/0.89          | ~ (v1_xboole_0 @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['31', '59'])).
% 0.69/0.89  thf('61', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.69/0.89          | ~ (v1_relat_1 @ X1)
% 0.69/0.89          | ~ (v1_xboole_0 @ X0))),
% 0.69/0.89      inference('simplify', [status(thm)], ['60'])).
% 0.69/0.89  thf('62', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_xboole_0 @ X1)
% 0.69/0.89          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['30', '61'])).
% 0.69/0.89  thf('63', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.69/0.89          | ~ (v1_relat_1 @ X1)
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.69/0.89          | ~ (v1_relat_1 @ X1))),
% 0.69/0.89      inference('sup+', [status(thm)], ['29', '62'])).
% 0.69/0.89  thf('64', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ X1)
% 0.69/0.89          | ((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['63'])).
% 0.69/0.89  thf('65', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.89          | ((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['28', '64'])).
% 0.69/0.89  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.89  thf('67', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.69/0.89  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.89  thf('69', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['67', '68'])).
% 0.69/0.89  thf('70', plain,
% 0.69/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['7', '10'])).
% 0.69/0.89  thf('71', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['69', '70'])).
% 0.69/0.89  thf('72', plain,
% 0.69/0.89      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.89  thf('73', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['1', '27'])).
% 0.69/0.89  thf('74', plain,
% 0.69/0.89      (![X0 : $i]: (((k4_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['72', '73'])).
% 0.69/0.89  thf('75', plain,
% 0.69/0.89      (![X44 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X44)) | ~ (v1_relat_1 @ X44))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.69/0.89  thf('76', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((v1_relat_1 @ k1_xboole_0)
% 0.69/0.89          | ~ (v1_xboole_0 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['74', '75'])).
% 0.69/0.89  thf('77', plain, (![X43 : $i]: ((v1_relat_1 @ X43) | ~ (v1_xboole_0 @ X43))),
% 0.69/0.89      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.69/0.89  thf('78', plain,
% 0.69/0.89      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.69/0.89      inference('clc', [status(thm)], ['76', '77'])).
% 0.69/0.89  thf('79', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.69/0.89      inference('sup-', [status(thm)], ['71', '78'])).
% 0.69/0.89  thf('80', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['65', '66', '79'])).
% 0.69/0.89  thf(involutiveness_k4_relat_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.69/0.89  thf('81', plain,
% 0.69/0.89      (![X47 : $i]:
% 0.69/0.89         (((k4_relat_1 @ (k4_relat_1 @ X47)) = (X47)) | ~ (v1_relat_1 @ X47))),
% 0.69/0.89      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.69/0.89  thf('82', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['80', '81'])).
% 0.69/0.89  thf('83', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['1', '27'])).
% 0.69/0.89  thf('84', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.89      inference('demod', [status(thm)], ['82', '83'])).
% 0.69/0.89  thf('85', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ k1_xboole_0)
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['0', '84'])).
% 0.69/0.89  thf('86', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.69/0.89      inference('sup-', [status(thm)], ['71', '78'])).
% 0.69/0.89  thf('87', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.89      inference('demod', [status(thm)], ['85', '86'])).
% 0.69/0.89  thf('88', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('simplify', [status(thm)], ['87'])).
% 0.69/0.89  thf('89', plain,
% 0.69/0.89      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.89  thf('90', plain,
% 0.69/0.89      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.69/0.89        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('91', plain,
% 0.69/0.89      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.69/0.89         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.69/0.89      inference('split', [status(esa)], ['90'])).
% 0.69/0.89  thf('92', plain,
% 0.69/0.89      ((![X0 : $i]:
% 0.69/0.89          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.69/0.89         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['89', '91'])).
% 0.69/0.89  thf('93', plain,
% 0.69/0.89      (![X45 : $i, X46 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X45)
% 0.69/0.89          | ~ (v1_relat_1 @ X46)
% 0.69/0.89          | (v1_relat_1 @ (k5_relat_1 @ X45 @ X46)))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.69/0.89  thf('94', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.69/0.89  thf('95', plain,
% 0.69/0.89      (![X51 : $i, X52 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X51)
% 0.69/0.89          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X52 @ X51)) @ 
% 0.69/0.89             (k1_relat_1 @ X52))
% 0.69/0.89          | ~ (v1_relat_1 @ X52))),
% 0.69/0.89      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.69/0.89  thf('96', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.69/0.89           k1_xboole_0)
% 0.69/0.89          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['94', '95'])).
% 0.69/0.89  thf('97', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.69/0.89      inference('sup-', [status(thm)], ['71', '78'])).
% 0.69/0.89  thf('98', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.69/0.89           k1_xboole_0)
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['96', '97'])).
% 0.69/0.89  thf('99', plain,
% 0.69/0.89      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['18', '19'])).
% 0.69/0.89  thf('100', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['98', '99'])).
% 0.69/0.89  thf('101', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k1_xboole_0) = (X0))
% 0.69/0.89          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['50', '53'])).
% 0.69/0.89  thf('102', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.69/0.89          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['100', '101'])).
% 0.69/0.89  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.89  thf('104', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.69/0.89          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.69/0.89      inference('demod', [status(thm)], ['102', '103'])).
% 0.69/0.89  thf('105', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.69/0.89          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['93', '104'])).
% 0.69/0.89  thf('106', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.69/0.89      inference('sup-', [status(thm)], ['71', '78'])).
% 0.69/0.89  thf('107', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['105', '106'])).
% 0.69/0.89  thf('108', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('simplify', [status(thm)], ['107'])).
% 0.69/0.89  thf('109', plain,
% 0.69/0.89      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.89  thf('110', plain,
% 0.69/0.89      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.69/0.89         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.89      inference('split', [status(esa)], ['90'])).
% 0.69/0.89  thf('111', plain,
% 0.69/0.89      ((![X0 : $i]:
% 0.69/0.89          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.69/0.89         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['109', '110'])).
% 0.69/0.89  thf('112', plain,
% 0.69/0.89      (((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.89         | ~ (v1_relat_1 @ sk_A)
% 0.69/0.89         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.69/0.89         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['108', '111'])).
% 0.69/0.89  thf('113', plain, ((v1_relat_1 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.89  thf('115', plain,
% 0.69/0.89      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.69/0.89         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.89      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.69/0.89  thf('116', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.69/0.89      inference('simplify', [status(thm)], ['115'])).
% 0.69/0.89  thf('117', plain,
% 0.69/0.89      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.69/0.89       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.69/0.89      inference('split', [status(esa)], ['90'])).
% 0.69/0.89  thf('118', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.69/0.89      inference('sat_resolution*', [status(thm)], ['116', '117'])).
% 0.69/0.89  thf('119', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.89      inference('simpl_trail', [status(thm)], ['92', '118'])).
% 0.69/0.89  thf('120', plain,
% 0.69/0.89      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.89        | ~ (v1_relat_1 @ sk_A)
% 0.69/0.89        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['88', '119'])).
% 0.69/0.89  thf('121', plain, ((v1_relat_1 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('122', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.89  thf('123', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['120', '121', '122'])).
% 0.69/0.89  thf('124', plain, ($false), inference('simplify', [status(thm)], ['123'])).
% 0.69/0.89  
% 0.69/0.89  % SZS output end Refutation
% 0.69/0.89  
% 0.69/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
