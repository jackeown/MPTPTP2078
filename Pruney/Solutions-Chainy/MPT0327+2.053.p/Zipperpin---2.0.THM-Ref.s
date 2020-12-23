%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hB5Ubma633

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:57 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  107 (1393 expanded)
%              Number of leaves         :   27 ( 442 expanded)
%              Depth                    :   22
%              Number of atoms          :  740 (10105 expanded)
%              Number of equality atoms :   76 (1095 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X41 ) @ X43 )
      | ~ ( r2_hidden @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X19: $i] :
      ( ( k2_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('25',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('26',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 != X50 )
      | ~ ( r2_hidden @ X48 @ ( k4_xboole_0 @ X49 @ ( k1_tarski @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('27',plain,(
    ! [X49: $i,X50: $i] :
      ~ ( r2_hidden @ X50 @ ( k4_xboole_0 @ X49 @ ( k1_tarski @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['4','35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( r2_hidden @ X48 @ X49 )
      | ~ ( r2_hidden @ X48 @ ( k4_xboole_0 @ X49 @ ( k1_tarski @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    r1_tarski @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('45',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','34'])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('51',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('53',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49','54'])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49','54'])).

thf('57',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('58',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('60',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('61',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','33'])).

thf('63',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['55','63'])).

thf('65',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('66',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['55','63'])).

thf('68',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','33'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['66','71'])).

thf('73',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['4','35'])).

thf('75',plain,(
    ( k2_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('77',plain,(
    ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hB5Ubma633
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.69  % Solved by: fo/fo7.sh
% 0.47/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.69  % done 631 iterations in 0.240s
% 0.47/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.69  % SZS output start Refutation
% 0.47/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.69  thf(t140_zfmisc_1, conjecture,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( r2_hidden @ A @ B ) =>
% 0.47/0.69       ( ( k2_xboole_0 @
% 0.47/0.69           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.47/0.69         ( B ) ) ))).
% 0.47/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.69    (~( ![A:$i,B:$i]:
% 0.47/0.69        ( ( r2_hidden @ A @ B ) =>
% 0.47/0.69          ( ( k2_xboole_0 @
% 0.47/0.69              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.47/0.69            ( B ) ) ) )),
% 0.47/0.69    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.47/0.69  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(l1_zfmisc_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.47/0.69  thf('1', plain,
% 0.47/0.69      (![X41 : $i, X43 : $i]:
% 0.47/0.69         ((r1_tarski @ (k1_tarski @ X41) @ X43) | ~ (r2_hidden @ X41 @ X43))),
% 0.47/0.69      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.47/0.69  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.47/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.69  thf(t12_xboole_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.47/0.69  thf('3', plain,
% 0.47/0.69      (![X17 : $i, X18 : $i]:
% 0.47/0.69         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 0.47/0.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.69  thf('4', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.47/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.69  thf(t98_xboole_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.47/0.69  thf('5', plain,
% 0.47/0.69      (![X29 : $i, X30 : $i]:
% 0.47/0.69         ((k2_xboole_0 @ X29 @ X30)
% 0.47/0.69           = (k5_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.47/0.69  thf(d10_xboole_0, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.69  thf('6', plain,
% 0.47/0.69      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 0.47/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.69  thf('7', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.47/0.69      inference('simplify', [status(thm)], ['6'])).
% 0.47/0.69  thf(l32_xboole_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.69  thf('8', plain,
% 0.47/0.69      (![X12 : $i, X14 : $i]:
% 0.47/0.69         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.47/0.69          | ~ (r1_tarski @ X12 @ X14))),
% 0.47/0.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.47/0.69  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.69  thf(t51_xboole_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.47/0.69       ( A ) ))).
% 0.47/0.69  thf('10', plain,
% 0.47/0.69      (![X21 : $i, X22 : $i]:
% 0.47/0.69         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.47/0.69           = (X21))),
% 0.47/0.69      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.47/0.69  thf('11', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (X0))),
% 0.47/0.69      inference('sup+', [status(thm)], ['9', '10'])).
% 0.47/0.69  thf(t1_boole, axiom,
% 0.47/0.69    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.69  thf('12', plain, (![X19 : $i]: ((k2_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.47/0.69      inference('cnf', [status(esa)], [t1_boole])).
% 0.47/0.69  thf('13', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.47/0.69      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.69  thf(t100_xboole_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.47/0.69  thf('14', plain,
% 0.47/0.69      (![X15 : $i, X16 : $i]:
% 0.47/0.69         ((k4_xboole_0 @ X15 @ X16)
% 0.47/0.69           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.69  thf('15', plain,
% 0.47/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.47/0.69      inference('sup+', [status(thm)], ['13', '14'])).
% 0.47/0.69  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.69  thf('17', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.69      inference('sup+', [status(thm)], ['15', '16'])).
% 0.47/0.69  thf(t91_xboole_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.47/0.69       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.47/0.69  thf('18', plain,
% 0.47/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ X28)
% 0.47/0.69           = (k5_xboole_0 @ X26 @ (k5_xboole_0 @ X27 @ X28)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.47/0.69  thf('19', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.47/0.69           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.69      inference('sup+', [status(thm)], ['17', '18'])).
% 0.47/0.69  thf(t3_boole, axiom,
% 0.47/0.69    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.69  thf('20', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.47/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.69  thf('21', plain,
% 0.47/0.69      (![X29 : $i, X30 : $i]:
% 0.47/0.69         ((k2_xboole_0 @ X29 @ X30)
% 0.47/0.69           = (k5_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.47/0.69  thf('22', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.47/0.69      inference('sup+', [status(thm)], ['20', '21'])).
% 0.47/0.69  thf(d3_tarski, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.69  thf('23', plain,
% 0.47/0.69      (![X1 : $i, X3 : $i]:
% 0.47/0.69         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.69  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.69  thf(t69_enumset1, axiom,
% 0.47/0.69    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.69  thf('25', plain,
% 0.47/0.69      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.47/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.69  thf(t64_zfmisc_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.47/0.69       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.47/0.69  thf('26', plain,
% 0.47/0.69      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.47/0.69         (((X48) != (X50))
% 0.47/0.69          | ~ (r2_hidden @ X48 @ (k4_xboole_0 @ X49 @ (k1_tarski @ X50))))),
% 0.47/0.69      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.47/0.69  thf('27', plain,
% 0.47/0.69      (![X49 : $i, X50 : $i]:
% 0.47/0.69         ~ (r2_hidden @ X50 @ (k4_xboole_0 @ X49 @ (k1_tarski @ X50)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['26'])).
% 0.47/0.69  thf('28', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['25', '27'])).
% 0.47/0.69  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.47/0.69      inference('sup-', [status(thm)], ['24', '28'])).
% 0.47/0.69  thf('30', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.47/0.69      inference('sup-', [status(thm)], ['23', '29'])).
% 0.47/0.69  thf('31', plain,
% 0.47/0.69      (![X17 : $i, X18 : $i]:
% 0.47/0.69         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 0.47/0.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.69  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.69  thf('33', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.47/0.69      inference('demod', [status(thm)], ['22', '32'])).
% 0.47/0.69  thf('34', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['19', '33'])).
% 0.47/0.69  thf('35', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.47/0.69           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.69      inference('sup+', [status(thm)], ['5', '34'])).
% 0.47/0.69  thf('36', plain,
% 0.47/0.69      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.47/0.69         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.47/0.69      inference('sup+', [status(thm)], ['4', '35'])).
% 0.47/0.69  thf('37', plain,
% 0.47/0.69      (![X1 : $i, X3 : $i]:
% 0.47/0.69         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.69  thf('38', plain,
% 0.47/0.69      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.47/0.69         ((r2_hidden @ X48 @ X49)
% 0.47/0.69          | ~ (r2_hidden @ X48 @ (k4_xboole_0 @ X49 @ (k1_tarski @ X50))))),
% 0.47/0.69      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.47/0.69  thf('39', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.69         ((r1_tarski @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)
% 0.47/0.69          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))) @ 
% 0.47/0.69             X1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.69  thf('40', plain,
% 0.47/0.69      (![X1 : $i, X3 : $i]:
% 0.47/0.69         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.69  thf('41', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)
% 0.47/0.69          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.69  thf('42', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)),
% 0.47/0.69      inference('simplify', [status(thm)], ['41'])).
% 0.47/0.69  thf('43', plain,
% 0.47/0.69      ((r1_tarski @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.47/0.69      inference('sup+', [status(thm)], ['36', '42'])).
% 0.47/0.69  thf('44', plain,
% 0.47/0.69      (![X17 : $i, X18 : $i]:
% 0.47/0.69         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 0.47/0.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.69  thf('45', plain,
% 0.47/0.69      (((k2_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)
% 0.47/0.69         = (sk_B))),
% 0.47/0.69      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.69  thf('46', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.47/0.69           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.69      inference('sup+', [status(thm)], ['5', '34'])).
% 0.47/0.69  thf('47', plain,
% 0.47/0.69      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.47/0.69         = (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B))),
% 0.47/0.69      inference('sup+', [status(thm)], ['45', '46'])).
% 0.47/0.69  thf('48', plain,
% 0.47/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ X28)
% 0.47/0.69           = (k5_xboole_0 @ X26 @ (k5_xboole_0 @ X27 @ X28)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.47/0.69  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.69      inference('sup+', [status(thm)], ['15', '16'])).
% 0.47/0.69  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.69  thf('51', plain,
% 0.47/0.69      (![X29 : $i, X30 : $i]:
% 0.47/0.69         ((k2_xboole_0 @ X29 @ X30)
% 0.47/0.69           = (k5_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.47/0.69  thf('52', plain,
% 0.47/0.69      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.69      inference('sup+', [status(thm)], ['50', '51'])).
% 0.47/0.69  thf(idempotence_k2_xboole_0, axiom,
% 0.47/0.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.47/0.69  thf('53', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.47/0.69      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.47/0.69  thf('54', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.69  thf('55', plain,
% 0.47/0.69      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.47/0.69         = (k1_tarski @ sk_A))),
% 0.47/0.69      inference('demod', [status(thm)], ['47', '48', '49', '54'])).
% 0.47/0.69  thf('56', plain,
% 0.47/0.69      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.47/0.69         = (k1_tarski @ sk_A))),
% 0.47/0.69      inference('demod', [status(thm)], ['47', '48', '49', '54'])).
% 0.47/0.69  thf('57', plain,
% 0.47/0.69      (![X29 : $i, X30 : $i]:
% 0.47/0.69         ((k2_xboole_0 @ X29 @ X30)
% 0.47/0.69           = (k5_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.47/0.69  thf('58', plain,
% 0.47/0.69      (((k2_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)
% 0.47/0.69         = (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.47/0.69            (k1_tarski @ sk_A)))),
% 0.47/0.69      inference('sup+', [status(thm)], ['56', '57'])).
% 0.47/0.69  thf('59', plain,
% 0.47/0.69      (((k2_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)
% 0.47/0.69         = (sk_B))),
% 0.47/0.69      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.69  thf('60', plain,
% 0.47/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ X28)
% 0.47/0.69           = (k5_xboole_0 @ X26 @ (k5_xboole_0 @ X27 @ X28)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.47/0.69  thf('61', plain,
% 0.47/0.69      (((sk_B)
% 0.47/0.69         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.47/0.69            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.47/0.69      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.47/0.69  thf('62', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['19', '33'])).
% 0.47/0.69  thf('63', plain,
% 0.47/0.69      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.47/0.69         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.47/0.69      inference('sup+', [status(thm)], ['61', '62'])).
% 0.47/0.69  thf('64', plain,
% 0.47/0.69      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.47/0.69         = (k1_tarski @ sk_A))),
% 0.47/0.69      inference('demod', [status(thm)], ['55', '63'])).
% 0.47/0.69  thf('65', plain,
% 0.47/0.69      (![X21 : $i, X22 : $i]:
% 0.47/0.69         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.47/0.69           = (X21))),
% 0.47/0.69      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.47/0.69  thf('66', plain,
% 0.47/0.69      (((k2_xboole_0 @ 
% 0.47/0.69         (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.47/0.69         (k1_tarski @ sk_A)) = (sk_B))),
% 0.47/0.69      inference('sup+', [status(thm)], ['64', '65'])).
% 0.47/0.69  thf('67', plain,
% 0.47/0.69      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.47/0.69         = (k1_tarski @ sk_A))),
% 0.47/0.69      inference('demod', [status(thm)], ['55', '63'])).
% 0.47/0.69  thf('68', plain,
% 0.47/0.69      (![X15 : $i, X16 : $i]:
% 0.47/0.69         ((k4_xboole_0 @ X15 @ X16)
% 0.47/0.69           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.69  thf('69', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['19', '33'])).
% 0.47/0.69  thf('70', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((k3_xboole_0 @ X1 @ X0)
% 0.47/0.69           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.47/0.69      inference('sup+', [status(thm)], ['68', '69'])).
% 0.47/0.69  thf('71', plain,
% 0.47/0.69      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.47/0.69         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.47/0.69      inference('sup+', [status(thm)], ['67', '70'])).
% 0.47/0.69  thf('72', plain,
% 0.47/0.69      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.47/0.69         (k1_tarski @ sk_A)) = (sk_B))),
% 0.47/0.69      inference('demod', [status(thm)], ['66', '71'])).
% 0.47/0.69  thf('73', plain,
% 0.47/0.69      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.47/0.69         (k1_tarski @ sk_A)) != (sk_B))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('74', plain,
% 0.47/0.69      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.47/0.69         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.47/0.69      inference('sup+', [status(thm)], ['4', '35'])).
% 0.47/0.69  thf('75', plain,
% 0.47/0.69      (((k2_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.47/0.69         (k1_tarski @ sk_A)) != (sk_B))),
% 0.47/0.69      inference('demod', [status(thm)], ['73', '74'])).
% 0.47/0.69  thf('76', plain,
% 0.47/0.69      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.47/0.69         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.47/0.69      inference('sup+', [status(thm)], ['61', '62'])).
% 0.47/0.69  thf('77', plain,
% 0.47/0.69      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.47/0.69         (k1_tarski @ sk_A)) != (sk_B))),
% 0.47/0.69      inference('demod', [status(thm)], ['75', '76'])).
% 0.47/0.69  thf('78', plain, ($false),
% 0.47/0.69      inference('simplify_reflect-', [status(thm)], ['72', '77'])).
% 0.47/0.69  
% 0.47/0.69  % SZS output end Refutation
% 0.47/0.69  
% 0.47/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
