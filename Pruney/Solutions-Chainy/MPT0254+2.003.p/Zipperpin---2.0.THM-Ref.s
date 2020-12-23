%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0FLbKnm3AY

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:37 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  138 (1811 expanded)
%              Number of leaves         :   31 ( 626 expanded)
%              Depth                    :   23
%              Number of atoms          :  972 (15393 expanded)
%              Number of equality atoms :  110 (1760 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ X51 @ X52 )
      | ( r2_hidden @ X51 @ X53 )
      | ( X53
       != ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r2_hidden @ X51 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X51 @ X52 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k1_zfmisc_1 @ X0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( r2_hidden @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('30',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','35','36','37'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('39',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['48','49'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['48','49'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('57',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['48','49'])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('60',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('62',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['63'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('70',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','68','81'])).

thf('83',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','68','81'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('84',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('85',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('88',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['86','93'])).

thf('95',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['83','94'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('96',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('97',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','97'])).

thf('99',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','98'])).

thf('100',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('102',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','97'])).

thf('104',plain,(
    r2_hidden @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['99','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0FLbKnm3AY
% 0.14/0.37  % Computer   : n010.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:06:00 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 404 iterations in 0.162s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(t1_zfmisc_1, axiom,
% 0.38/0.61    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.38/0.61  thf('0', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.38/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.61  thf('1', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.38/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.61  thf(d1_zfmisc_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.38/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.38/0.61  thf('2', plain,
% 0.38/0.61      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.38/0.61         (~ (r1_tarski @ X51 @ X52)
% 0.38/0.61          | (r2_hidden @ X51 @ X53)
% 0.38/0.61          | ((X53) != (k1_zfmisc_1 @ X52)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.38/0.61  thf('3', plain,
% 0.38/0.61      (![X51 : $i, X52 : $i]:
% 0.38/0.61         ((r2_hidden @ X51 @ (k1_zfmisc_1 @ X52)) | ~ (r1_tarski @ X51 @ X52))),
% 0.38/0.61      inference('simplify', [status(thm)], ['2'])).
% 0.38/0.61  thf('4', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['1', '3'])).
% 0.38/0.61  thf(antisymmetry_r2_hidden, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.38/0.61  thf('5', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.61      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      (![X0 : $i]: ~ (r2_hidden @ (k1_zfmisc_1 @ X0) @ k1_xboole_0)),
% 0.38/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.61  thf('7', plain, (~ (r2_hidden @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0)),
% 0.38/0.61      inference('sup-', [status(thm)], ['0', '6'])).
% 0.38/0.61  thf(t49_zfmisc_1, conjecture,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i,B:$i]:
% 0.38/0.61        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.38/0.61  thf('8', plain,
% 0.38/0.61      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(commutativity_k5_xboole_0, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.38/0.61  thf('9', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.38/0.61  thf(t94_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k2_xboole_0 @ A @ B ) =
% 0.38/0.61       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.61  thf('10', plain,
% 0.38/0.61      (![X21 : $i, X22 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X21 @ X22)
% 0.38/0.61           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 0.38/0.61              (k3_xboole_0 @ X21 @ X22)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      (![X21 : $i, X22 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X21 @ X22)
% 0.38/0.61           = (k5_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ 
% 0.38/0.61              (k5_xboole_0 @ X21 @ X22)))),
% 0.38/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X0 @ X1)
% 0.38/0.61           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['9', '12'])).
% 0.38/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      (![X21 : $i, X22 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X21 @ X22)
% 0.38/0.61           = (k5_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ 
% 0.38/0.61              (k5_xboole_0 @ X21 @ X22)))),
% 0.38/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X0 @ X1)
% 0.38/0.61           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.61  thf('17', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['13', '16'])).
% 0.38/0.61  thf('18', plain,
% 0.38/0.61      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['8', '17'])).
% 0.38/0.61  thf('19', plain,
% 0.38/0.61      (![X21 : $i, X22 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X21 @ X22)
% 0.38/0.61           = (k5_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ 
% 0.38/0.61              (k5_xboole_0 @ X21 @ X22)))),
% 0.38/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.38/0.61  thf('20', plain,
% 0.38/0.61      (![X21 : $i, X22 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X21 @ X22)
% 0.38/0.61           = (k5_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ 
% 0.38/0.61              (k5_xboole_0 @ X21 @ X22)))),
% 0.38/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.38/0.61  thf('21', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.38/0.61           = (k5_xboole_0 @ 
% 0.38/0.61              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.38/0.61              (k2_xboole_0 @ X1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['19', '20'])).
% 0.38/0.61  thf('22', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.38/0.61  thf('23', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.38/0.61           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.38/0.61              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.38/0.61      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.61  thf('24', plain,
% 0.38/0.61      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.61         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.38/0.61         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.38/0.61            (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.61             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.38/0.61      inference('sup+', [status(thm)], ['18', '23'])).
% 0.38/0.61  thf('25', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.38/0.61  thf(t5_boole, axiom,
% 0.38/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.61  thf('26', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.38/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.61  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['25', '26'])).
% 0.38/0.61  thf('28', plain,
% 0.38/0.61      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.61         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.38/0.61         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.61            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.38/0.61      inference('demod', [status(thm)], ['24', '27'])).
% 0.38/0.61  thf('29', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X0 @ X1)
% 0.38/0.61           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.61  thf('30', plain,
% 0.38/0.61      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.61         (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.38/0.61         = (k5_xboole_0 @ 
% 0.38/0.61            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.61             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.38/0.61            (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.61             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.38/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.38/0.61  thf('31', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['13', '16'])).
% 0.38/0.61  thf(t91_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.38/0.61       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.61         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.38/0.61           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.61  thf('33', plain,
% 0.38/0.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.61  thf(t100_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.61  thf('34', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X9 @ X10)
% 0.38/0.61           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.61  thf('35', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['33', '34'])).
% 0.38/0.61  thf('36', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.38/0.61  thf('37', plain,
% 0.38/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.61         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.38/0.61           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.61  thf('38', plain,
% 0.38/0.61      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.61         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.38/0.61         = (k5_xboole_0 @ sk_B @ 
% 0.38/0.61            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.38/0.61             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.61              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.38/0.61      inference('demod', [status(thm)], ['30', '31', '32', '35', '36', '37'])).
% 0.38/0.61  thf(t92_xboole_1, axiom,
% 0.38/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.61  thf('39', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.61  thf('40', plain,
% 0.38/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.61         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.38/0.61           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.61  thf('41', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.61           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['39', '40'])).
% 0.38/0.61  thf('42', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['25', '26'])).
% 0.38/0.61  thf('43', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.61      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.61  thf('44', plain,
% 0.38/0.61      (((k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.38/0.61         (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.61          (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.38/0.61         = (k5_xboole_0 @ sk_B @ 
% 0.38/0.61            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.61             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.38/0.61      inference('sup+', [status(thm)], ['38', '43'])).
% 0.38/0.61  thf('45', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.38/0.61  thf('46', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.61      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.61  thf('47', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['45', '46'])).
% 0.38/0.61  thf('48', plain,
% 0.38/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.38/0.61         = (k5_xboole_0 @ 
% 0.38/0.61            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.61             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.38/0.61            (k5_xboole_0 @ sk_B @ 
% 0.38/0.61             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.61              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.38/0.61      inference('sup+', [status(thm)], ['44', '47'])).
% 0.38/0.61  thf('49', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['45', '46'])).
% 0.38/0.61  thf('50', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.61  thf(t48_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.61  thf('51', plain,
% 0.38/0.61      (![X14 : $i, X15 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.38/0.61           = (k3_xboole_0 @ X14 @ X15))),
% 0.38/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.61  thf('52', plain,
% 0.38/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.38/0.61         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.38/0.61      inference('sup+', [status(thm)], ['50', '51'])).
% 0.38/0.61  thf('53', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.61  thf('54', plain,
% 0.38/0.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.61  thf('55', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.38/0.61      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.38/0.61  thf('56', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['33', '34'])).
% 0.38/0.61  thf('57', plain,
% 0.38/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.38/0.61         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.38/0.61      inference('sup+', [status(thm)], ['55', '56'])).
% 0.38/0.61  thf('58', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.61  thf('59', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.38/0.61  thf('60', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.38/0.61      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.38/0.61  thf('61', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.61      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.61  thf('62', plain, (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.38/0.61      inference('sup+', [status(thm)], ['60', '61'])).
% 0.38/0.61  thf(d10_xboole_0, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.61  thf('63', plain,
% 0.38/0.61      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.61  thf('64', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.38/0.61      inference('simplify', [status(thm)], ['63'])).
% 0.38/0.61  thf(t28_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.61  thf('65', plain,
% 0.38/0.61      (![X11 : $i, X12 : $i]:
% 0.38/0.61         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.38/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.61  thf('66', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.38/0.61  thf('67', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X9 @ X10)
% 0.38/0.61           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.61  thf('68', plain,
% 0.38/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['66', '67'])).
% 0.38/0.61  thf('69', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.38/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.61  thf('70', plain,
% 0.38/0.61      (![X11 : $i, X12 : $i]:
% 0.38/0.61         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.38/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.61  thf('71', plain,
% 0.38/0.61      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['69', '70'])).
% 0.38/0.61  thf('72', plain,
% 0.38/0.61      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.61  thf('73', plain,
% 0.38/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['71', '72'])).
% 0.38/0.61  thf('74', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X9 @ X10)
% 0.38/0.61           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.61  thf('75', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['73', '74'])).
% 0.38/0.61  thf('76', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.38/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.61  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['75', '76'])).
% 0.38/0.61  thf('78', plain,
% 0.38/0.61      (![X14 : $i, X15 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.38/0.61           = (k3_xboole_0 @ X14 @ X15))),
% 0.38/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.61  thf('79', plain,
% 0.38/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['77', '78'])).
% 0.38/0.61  thf('80', plain,
% 0.38/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['71', '72'])).
% 0.38/0.61  thf('81', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['79', '80'])).
% 0.38/0.61  thf('82', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['62', '68', '81'])).
% 0.38/0.61  thf('83', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['62', '68', '81'])).
% 0.38/0.61  thf(t69_enumset1, axiom,
% 0.38/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.61  thf('84', plain,
% 0.38/0.61      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.38/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.61  thf(l51_zfmisc_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.61  thf('85', plain,
% 0.38/0.61      (![X56 : $i, X57 : $i]:
% 0.38/0.61         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 0.38/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.61  thf('86', plain,
% 0.38/0.61      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['84', '85'])).
% 0.38/0.61  thf('87', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.38/0.61  thf('88', plain,
% 0.38/0.61      (![X21 : $i, X22 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X21 @ X22)
% 0.38/0.61           = (k5_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ 
% 0.38/0.61              (k5_xboole_0 @ X21 @ X22)))),
% 0.38/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.38/0.61  thf('89', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X0 @ X0)
% 0.38/0.61           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['87', '88'])).
% 0.38/0.61  thf('90', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.61  thf('91', plain,
% 0.38/0.61      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['89', '90'])).
% 0.38/0.61  thf('92', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.38/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.61  thf('93', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['91', '92'])).
% 0.38/0.61  thf('94', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['86', '93'])).
% 0.38/0.61  thf('95', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.38/0.61      inference('sup+', [status(thm)], ['83', '94'])).
% 0.38/0.61  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.38/0.61  thf('96', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.38/0.61  thf('97', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['95', '96'])).
% 0.38/0.61  thf('98', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['82', '97'])).
% 0.38/0.61  thf('99', plain, (~ (r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.38/0.61      inference('demod', [status(thm)], ['7', '98'])).
% 0.38/0.61  thf('100', plain,
% 0.38/0.61      (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.38/0.61  thf('101', plain,
% 0.38/0.61      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['1', '3'])).
% 0.38/0.61  thf('102', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['100', '101'])).
% 0.38/0.61  thf('103', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['82', '97'])).
% 0.38/0.61  thf('104', plain, ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.38/0.61      inference('demod', [status(thm)], ['102', '103'])).
% 0.38/0.61  thf('105', plain, ($false), inference('demod', [status(thm)], ['99', '104'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
