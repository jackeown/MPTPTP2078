%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i5RCMhfMSo

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:16 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 132 expanded)
%              Number of leaves         :   31 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  609 ( 936 expanded)
%              Number of equality atoms :   57 (  87 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t178_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k2_tarski @ X41 @ X40 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_A ) )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k2_tarski @ X41 @ X40 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['33'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('35',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('49',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','46','47','50'])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['12','51'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('53',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k10_relat_1 @ X48 @ ( k2_xboole_0 @ X49 @ X50 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X48 @ X49 ) @ ( k10_relat_1 @ X48 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i5RCMhfMSo
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.45/1.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.45/1.64  % Solved by: fo/fo7.sh
% 1.45/1.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.45/1.64  % done 2834 iterations in 1.196s
% 1.45/1.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.45/1.64  % SZS output start Refutation
% 1.45/1.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.45/1.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.45/1.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.45/1.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.45/1.64  thf(sk_C_type, type, sk_C: $i).
% 1.45/1.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.45/1.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.45/1.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.45/1.64  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.45/1.64  thf(sk_A_type, type, sk_A: $i).
% 1.45/1.64  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.45/1.64  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.45/1.64  thf(sk_B_type, type, sk_B: $i).
% 1.45/1.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.45/1.64  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.45/1.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.45/1.65  thf(t178_relat_1, conjecture,
% 1.45/1.65    (![A:$i,B:$i,C:$i]:
% 1.45/1.65     ( ( v1_relat_1 @ C ) =>
% 1.45/1.65       ( ( r1_tarski @ A @ B ) =>
% 1.45/1.65         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.45/1.65  thf(zf_stmt_0, negated_conjecture,
% 1.45/1.65    (~( ![A:$i,B:$i,C:$i]:
% 1.45/1.65        ( ( v1_relat_1 @ C ) =>
% 1.45/1.65          ( ( r1_tarski @ A @ B ) =>
% 1.45/1.65            ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 1.45/1.65    inference('cnf.neg', [status(esa)], [t178_relat_1])).
% 1.45/1.65  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.45/1.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.65  thf(t28_xboole_1, axiom,
% 1.45/1.65    (![A:$i,B:$i]:
% 1.45/1.65     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.45/1.65  thf('1', plain,
% 1.45/1.65      (![X24 : $i, X25 : $i]:
% 1.45/1.65         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 1.45/1.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.45/1.65  thf('2', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.45/1.65      inference('sup-', [status(thm)], ['0', '1'])).
% 1.45/1.65  thf(commutativity_k2_tarski, axiom,
% 1.45/1.65    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.45/1.65  thf('3', plain,
% 1.45/1.65      (![X40 : $i, X41 : $i]:
% 1.45/1.65         ((k2_tarski @ X41 @ X40) = (k2_tarski @ X40 @ X41))),
% 1.45/1.65      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.45/1.65  thf(t12_setfam_1, axiom,
% 1.45/1.65    (![A:$i,B:$i]:
% 1.45/1.65     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.45/1.65  thf('4', plain,
% 1.45/1.65      (![X46 : $i, X47 : $i]:
% 1.45/1.65         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 1.45/1.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.45/1.65  thf('5', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.45/1.65      inference('sup+', [status(thm)], ['3', '4'])).
% 1.45/1.65  thf('6', plain,
% 1.45/1.65      (![X46 : $i, X47 : $i]:
% 1.45/1.65         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 1.45/1.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.45/1.65  thf('7', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.45/1.65      inference('sup+', [status(thm)], ['5', '6'])).
% 1.45/1.65  thf(t100_xboole_1, axiom,
% 1.45/1.65    (![A:$i,B:$i]:
% 1.45/1.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.45/1.65  thf('8', plain,
% 1.45/1.65      (![X16 : $i, X17 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ X16 @ X17)
% 1.45/1.65           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.45/1.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.45/1.65  thf('9', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ X0 @ X1)
% 1.45/1.65           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['7', '8'])).
% 1.45/1.65  thf('10', plain,
% 1.45/1.65      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_A))),
% 1.45/1.65      inference('sup+', [status(thm)], ['2', '9'])).
% 1.45/1.65  thf(t39_xboole_1, axiom,
% 1.45/1.65    (![A:$i,B:$i]:
% 1.45/1.65     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.45/1.65  thf('11', plain,
% 1.45/1.65      (![X28 : $i, X29 : $i]:
% 1.45/1.65         ((k2_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28))
% 1.45/1.65           = (k2_xboole_0 @ X28 @ X29))),
% 1.45/1.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.45/1.65  thf('12', plain,
% 1.45/1.65      (((k2_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_A))
% 1.45/1.65         = (k2_xboole_0 @ sk_A @ sk_B))),
% 1.45/1.65      inference('sup+', [status(thm)], ['10', '11'])).
% 1.45/1.65  thf('13', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.45/1.65      inference('sup-', [status(thm)], ['0', '1'])).
% 1.45/1.65  thf('14', plain,
% 1.45/1.65      (![X16 : $i, X17 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ X16 @ X17)
% 1.45/1.65           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.45/1.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.45/1.65  thf('15', plain,
% 1.45/1.65      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 1.45/1.65      inference('sup+', [status(thm)], ['13', '14'])).
% 1.45/1.65  thf('16', plain,
% 1.45/1.65      (![X28 : $i, X29 : $i]:
% 1.45/1.65         ((k2_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28))
% 1.45/1.65           = (k2_xboole_0 @ X28 @ X29))),
% 1.45/1.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.45/1.65  thf('17', plain,
% 1.45/1.65      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A))
% 1.45/1.65         = (k2_xboole_0 @ sk_B @ sk_A))),
% 1.45/1.65      inference('sup+', [status(thm)], ['15', '16'])).
% 1.45/1.65  thf('18', plain,
% 1.45/1.65      (![X40 : $i, X41 : $i]:
% 1.45/1.65         ((k2_tarski @ X41 @ X40) = (k2_tarski @ X40 @ X41))),
% 1.45/1.65      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.45/1.65  thf(l51_zfmisc_1, axiom,
% 1.45/1.65    (![A:$i,B:$i]:
% 1.45/1.65     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.45/1.65  thf('19', plain,
% 1.45/1.65      (![X44 : $i, X45 : $i]:
% 1.45/1.65         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 1.45/1.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.45/1.65  thf('20', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.45/1.65      inference('sup+', [status(thm)], ['18', '19'])).
% 1.45/1.65  thf('21', plain,
% 1.45/1.65      (![X44 : $i, X45 : $i]:
% 1.45/1.65         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 1.45/1.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.45/1.65  thf('22', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.45/1.65      inference('sup+', [status(thm)], ['20', '21'])).
% 1.45/1.65  thf('23', plain,
% 1.45/1.65      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A))
% 1.45/1.65         = (k2_xboole_0 @ sk_A @ sk_B))),
% 1.45/1.65      inference('demod', [status(thm)], ['17', '22'])).
% 1.45/1.65  thf(d4_xboole_0, axiom,
% 1.45/1.65    (![A:$i,B:$i,C:$i]:
% 1.45/1.65     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.45/1.65       ( ![D:$i]:
% 1.45/1.65         ( ( r2_hidden @ D @ C ) <=>
% 1.45/1.65           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.45/1.65  thf('24', plain,
% 1.45/1.65      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.45/1.65         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.45/1.65          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.45/1.65          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.45/1.65      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.45/1.65  thf(t17_xboole_1, axiom,
% 1.45/1.65    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.45/1.65  thf('25', plain,
% 1.45/1.65      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 1.45/1.65      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.45/1.65  thf(t3_xboole_1, axiom,
% 1.45/1.65    (![A:$i]:
% 1.45/1.65     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.45/1.65  thf('26', plain,
% 1.45/1.65      (![X31 : $i]:
% 1.45/1.65         (((X31) = (k1_xboole_0)) | ~ (r1_tarski @ X31 @ k1_xboole_0))),
% 1.45/1.65      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.45/1.65  thf('27', plain,
% 1.45/1.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.45/1.65      inference('sup-', [status(thm)], ['25', '26'])).
% 1.45/1.65  thf('28', plain,
% 1.45/1.65      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.45/1.65         (~ (r2_hidden @ X4 @ X3)
% 1.45/1.65          | (r2_hidden @ X4 @ X2)
% 1.45/1.65          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 1.45/1.65      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.45/1.65  thf('29', plain,
% 1.45/1.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.45/1.65         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.45/1.65      inference('simplify', [status(thm)], ['28'])).
% 1.45/1.65  thf('30', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 1.45/1.65      inference('sup-', [status(thm)], ['27', '29'])).
% 1.45/1.65  thf('31', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.65         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.45/1.65          | ((X1) = (k3_xboole_0 @ k1_xboole_0 @ X0))
% 1.45/1.65          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X2))),
% 1.45/1.65      inference('sup-', [status(thm)], ['24', '30'])).
% 1.45/1.65  thf('32', plain,
% 1.45/1.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.45/1.65      inference('sup-', [status(thm)], ['25', '26'])).
% 1.45/1.65  thf('33', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.65         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.45/1.65          | ((X1) = (k1_xboole_0))
% 1.45/1.65          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X2))),
% 1.45/1.65      inference('demod', [status(thm)], ['31', '32'])).
% 1.45/1.65  thf('34', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         ((r2_hidden @ (sk_D @ X0 @ X1 @ k1_xboole_0) @ X0)
% 1.45/1.65          | ((X0) = (k1_xboole_0)))),
% 1.45/1.65      inference('condensation', [status(thm)], ['33'])).
% 1.45/1.65  thf(idempotence_k3_xboole_0, axiom,
% 1.45/1.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.45/1.65  thf('35', plain, (![X12 : $i]: ((k3_xboole_0 @ X12 @ X12) = (X12))),
% 1.45/1.65      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.45/1.65  thf('36', plain,
% 1.45/1.65      (![X16 : $i, X17 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ X16 @ X17)
% 1.45/1.65           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.45/1.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.45/1.65  thf('37', plain,
% 1.45/1.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['35', '36'])).
% 1.45/1.65  thf(d5_xboole_0, axiom,
% 1.45/1.65    (![A:$i,B:$i,C:$i]:
% 1.45/1.65     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.45/1.65       ( ![D:$i]:
% 1.45/1.65         ( ( r2_hidden @ D @ C ) <=>
% 1.45/1.65           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.45/1.65  thf('38', plain,
% 1.45/1.65      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.45/1.65         (~ (r2_hidden @ X10 @ X9)
% 1.45/1.65          | (r2_hidden @ X10 @ X7)
% 1.45/1.65          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.45/1.65      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.45/1.65  thf('39', plain,
% 1.45/1.65      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.45/1.65         ((r2_hidden @ X10 @ X7)
% 1.45/1.65          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.45/1.65      inference('simplify', [status(thm)], ['38'])).
% 1.45/1.65  thf('40', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 1.45/1.65      inference('sup-', [status(thm)], ['37', '39'])).
% 1.45/1.65  thf('41', plain,
% 1.45/1.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['35', '36'])).
% 1.45/1.65  thf('42', plain,
% 1.45/1.65      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.45/1.65         (~ (r2_hidden @ X10 @ X9)
% 1.45/1.65          | ~ (r2_hidden @ X10 @ X8)
% 1.45/1.65          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.45/1.65      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.45/1.65  thf('43', plain,
% 1.45/1.65      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.45/1.65         (~ (r2_hidden @ X10 @ X8)
% 1.45/1.65          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.45/1.65      inference('simplify', [status(thm)], ['42'])).
% 1.45/1.65  thf('44', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 1.45/1.65          | ~ (r2_hidden @ X1 @ X0))),
% 1.45/1.65      inference('sup-', [status(thm)], ['41', '43'])).
% 1.45/1.65  thf('45', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 1.45/1.65      inference('clc', [status(thm)], ['40', '44'])).
% 1.45/1.65  thf('46', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.45/1.65      inference('sup-', [status(thm)], ['34', '45'])).
% 1.45/1.65  thf('47', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.45/1.65      inference('sup+', [status(thm)], ['20', '21'])).
% 1.45/1.65  thf('48', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.45/1.65      inference('sup+', [status(thm)], ['20', '21'])).
% 1.45/1.65  thf(t1_boole, axiom,
% 1.45/1.65    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.45/1.65  thf('49', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 1.45/1.65      inference('cnf', [status(esa)], [t1_boole])).
% 1.45/1.65  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['48', '49'])).
% 1.45/1.65  thf('51', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 1.45/1.65      inference('demod', [status(thm)], ['23', '46', '47', '50'])).
% 1.45/1.65  thf('52', plain,
% 1.45/1.65      (((k2_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 1.45/1.65      inference('demod', [status(thm)], ['12', '51'])).
% 1.45/1.65  thf(t175_relat_1, axiom,
% 1.45/1.65    (![A:$i,B:$i,C:$i]:
% 1.45/1.65     ( ( v1_relat_1 @ C ) =>
% 1.45/1.65       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 1.45/1.65         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.45/1.65  thf('53', plain,
% 1.45/1.65      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.45/1.65         (((k10_relat_1 @ X48 @ (k2_xboole_0 @ X49 @ X50))
% 1.45/1.65            = (k2_xboole_0 @ (k10_relat_1 @ X48 @ X49) @ 
% 1.45/1.65               (k10_relat_1 @ X48 @ X50)))
% 1.45/1.65          | ~ (v1_relat_1 @ X48))),
% 1.45/1.65      inference('cnf', [status(esa)], [t175_relat_1])).
% 1.45/1.65  thf(t7_xboole_1, axiom,
% 1.45/1.65    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.45/1.65  thf('54', plain,
% 1.45/1.65      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 1.45/1.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.45/1.65  thf('55', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.65         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 1.45/1.65           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.45/1.65          | ~ (v1_relat_1 @ X2))),
% 1.45/1.65      inference('sup+', [status(thm)], ['53', '54'])).
% 1.45/1.65  thf('56', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ (k10_relat_1 @ X0 @ sk_B))
% 1.45/1.65          | ~ (v1_relat_1 @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['52', '55'])).
% 1.45/1.65  thf('57', plain,
% 1.45/1.65      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 1.45/1.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.65  thf('58', plain, (~ (v1_relat_1 @ sk_C)),
% 1.45/1.65      inference('sup-', [status(thm)], ['56', '57'])).
% 1.45/1.65  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 1.45/1.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.65  thf('60', plain, ($false), inference('demod', [status(thm)], ['58', '59'])).
% 1.45/1.65  
% 1.45/1.65  % SZS output end Refutation
% 1.45/1.65  
% 1.45/1.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
