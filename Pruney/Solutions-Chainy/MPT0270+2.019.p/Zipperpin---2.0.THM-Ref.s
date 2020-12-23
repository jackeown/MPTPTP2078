%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VgOVellCTq

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:14 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 278 expanded)
%              Number of leaves         :   26 (  96 expanded)
%              Depth                    :   21
%              Number of atoms          :  684 (2103 expanded)
%              Number of equality atoms :   70 ( 225 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','24'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','31'])).

thf('33',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','24'])).

thf('36',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('42',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 != X54 )
      | ~ ( r2_hidden @ X52 @ ( k4_xboole_0 @ X53 @ ( k1_tarski @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('43',plain,(
    ! [X53: $i,X54: $i] :
      ~ ( r2_hidden @ X54 @ ( k4_xboole_0 @ X53 @ ( k1_tarski @ X54 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','44'])).

thf('46',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','45'])).

thf('47',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('48',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X50 ) @ X51 )
      | ( r2_hidden @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('66',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','45','65'])).

thf('67',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['64','66'])).

thf('68',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['47','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VgOVellCTq
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:38:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.76  % Solved by: fo/fo7.sh
% 0.52/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.76  % done 650 iterations in 0.302s
% 0.52/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.76  % SZS output start Refutation
% 0.52/0.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.52/0.76  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.52/0.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.76  thf(sk_B_type, type, sk_B: $i > $i).
% 0.52/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.76  thf(t67_zfmisc_1, conjecture,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.52/0.76       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.52/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.76    (~( ![A:$i,B:$i]:
% 0.52/0.76        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.52/0.76          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.52/0.76    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.52/0.76  thf('0', plain,
% 0.52/0.76      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.52/0.76        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('1', plain,
% 0.52/0.76      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.52/0.76      inference('split', [status(esa)], ['0'])).
% 0.52/0.76  thf('2', plain,
% 0.52/0.76      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.52/0.76       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.52/0.76      inference('split', [status(esa)], ['0'])).
% 0.52/0.76  thf('3', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ sk_B_1)
% 0.52/0.76        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('4', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.52/0.76      inference('split', [status(esa)], ['3'])).
% 0.52/0.76  thf('5', plain,
% 0.52/0.76      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.52/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.76      inference('split', [status(esa)], ['0'])).
% 0.52/0.76  thf(t100_xboole_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.52/0.76  thf('6', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ X12 @ X13)
% 0.52/0.76           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.76  thf(idempotence_k3_xboole_0, axiom,
% 0.52/0.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.52/0.76  thf('7', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.52/0.76      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.52/0.76  thf('8', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ X12 @ X13)
% 0.52/0.76           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.76  thf('9', plain,
% 0.52/0.76      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['7', '8'])).
% 0.52/0.76  thf('10', plain,
% 0.52/0.76      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['7', '8'])).
% 0.52/0.76  thf(l97_xboole_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.52/0.76  thf('11', plain,
% 0.52/0.76      (![X10 : $i, X11 : $i]:
% 0.52/0.76         (r1_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k5_xboole_0 @ X10 @ X11))),
% 0.52/0.76      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.52/0.76  thf('12', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['10', '11'])).
% 0.52/0.76  thf('13', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.52/0.76      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.52/0.76  thf('14', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.52/0.76      inference('demod', [status(thm)], ['12', '13'])).
% 0.52/0.76  thf(t7_xboole_0, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.52/0.76          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.52/0.76  thf('15', plain,
% 0.52/0.76      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.52/0.76      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.52/0.76  thf(t4_xboole_0, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.52/0.76            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.52/0.76       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.52/0.76            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.52/0.76  thf('16', plain,
% 0.52/0.76      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.52/0.76          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.52/0.76      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.52/0.76  thf('17', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.76  thf('18', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['14', '17'])).
% 0.52/0.76  thf(t36_xboole_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.52/0.76  thf('19', plain,
% 0.52/0.76      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.52/0.76      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.52/0.76  thf(t28_xboole_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.76  thf('20', plain,
% 0.52/0.76      (![X14 : $i, X15 : $i]:
% 0.52/0.76         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.52/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.76  thf('21', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.52/0.76           = (k4_xboole_0 @ X0 @ X1))),
% 0.52/0.76      inference('sup-', [status(thm)], ['19', '20'])).
% 0.52/0.76  thf(commutativity_k3_xboole_0, axiom,
% 0.52/0.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.52/0.76  thf('22', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.76  thf('23', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.52/0.76           = (k4_xboole_0 @ X0 @ X1))),
% 0.52/0.76      inference('demod', [status(thm)], ['21', '22'])).
% 0.52/0.76  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.76      inference('demod', [status(thm)], ['18', '23'])).
% 0.52/0.76  thf('25', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.76      inference('demod', [status(thm)], ['9', '24'])).
% 0.52/0.76  thf(t91_xboole_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.52/0.76       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.52/0.76  thf('26', plain,
% 0.52/0.76      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.76         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.52/0.76           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.52/0.76  thf('27', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.52/0.76           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.76      inference('sup+', [status(thm)], ['25', '26'])).
% 0.52/0.76  thf(commutativity_k5_xboole_0, axiom,
% 0.52/0.76    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.52/0.76  thf('28', plain,
% 0.52/0.76      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.76  thf(t5_boole, axiom,
% 0.52/0.76    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.76  thf('29', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.52/0.76      inference('cnf', [status(esa)], [t5_boole])).
% 0.52/0.76  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['28', '29'])).
% 0.52/0.76  thf('31', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.76      inference('demod', [status(thm)], ['27', '30'])).
% 0.52/0.76  thf('32', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((k3_xboole_0 @ X1 @ X0)
% 0.52/0.76           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.52/0.76      inference('sup+', [status(thm)], ['6', '31'])).
% 0.52/0.76  thf('33', plain,
% 0.52/0.76      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.52/0.76          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.52/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.76      inference('sup+', [status(thm)], ['5', '32'])).
% 0.52/0.76  thf('34', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.76  thf('35', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.76      inference('demod', [status(thm)], ['9', '24'])).
% 0.52/0.76  thf('36', plain,
% 0.52/0.76      ((((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.52/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.76      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.52/0.76  thf('37', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ X12 @ X13)
% 0.52/0.76           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.76  thf('38', plain,
% 0.52/0.76      ((((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.52/0.76          = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0)))
% 0.52/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.76      inference('sup+', [status(thm)], ['36', '37'])).
% 0.52/0.76  thf('39', plain,
% 0.52/0.76      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.76  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['28', '29'])).
% 0.52/0.76  thf('41', plain,
% 0.52/0.76      ((((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1)))
% 0.52/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.76      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.52/0.76  thf(t64_zfmisc_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.52/0.76       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.52/0.76  thf('42', plain,
% 0.52/0.76      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.52/0.76         (((X52) != (X54))
% 0.52/0.76          | ~ (r2_hidden @ X52 @ (k4_xboole_0 @ X53 @ (k1_tarski @ X54))))),
% 0.52/0.76      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.52/0.76  thf('43', plain,
% 0.52/0.76      (![X53 : $i, X54 : $i]:
% 0.52/0.76         ~ (r2_hidden @ X54 @ (k4_xboole_0 @ X53 @ (k1_tarski @ X54)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['42'])).
% 0.52/0.76  thf('44', plain,
% 0.52/0.76      ((~ (r2_hidden @ sk_A @ sk_B_1))
% 0.52/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['41', '43'])).
% 0.52/0.76  thf('45', plain,
% 0.52/0.76      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.52/0.76       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.52/0.76      inference('sup-', [status(thm)], ['4', '44'])).
% 0.52/0.76  thf('46', plain, (~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.52/0.76      inference('sat_resolution*', [status(thm)], ['2', '45'])).
% 0.52/0.76  thf('47', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.52/0.76      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.52/0.76  thf(l27_zfmisc_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.52/0.76  thf('48', plain,
% 0.52/0.76      (![X50 : $i, X51 : $i]:
% 0.52/0.76         ((r1_xboole_0 @ (k1_tarski @ X50) @ X51) | (r2_hidden @ X50 @ X51))),
% 0.52/0.76      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.52/0.76  thf('49', plain,
% 0.52/0.76      (![X5 : $i, X6 : $i]:
% 0.52/0.76         ((r1_xboole_0 @ X5 @ X6)
% 0.52/0.76          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.52/0.76  thf('50', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.76  thf('51', plain,
% 0.52/0.76      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.52/0.76          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.52/0.76      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.52/0.76  thf('52', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.76          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.52/0.76      inference('sup-', [status(thm)], ['50', '51'])).
% 0.52/0.76  thf('53', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.52/0.76      inference('sup-', [status(thm)], ['49', '52'])).
% 0.52/0.76  thf('54', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['48', '53'])).
% 0.52/0.76  thf('55', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.76  thf('56', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((r2_hidden @ X0 @ X1)
% 0.52/0.76          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['54', '55'])).
% 0.52/0.76  thf('57', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.76  thf('58', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ X12 @ X13)
% 0.52/0.76           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.76  thf('59', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ X0 @ X1)
% 0.52/0.76           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.76      inference('sup+', [status(thm)], ['57', '58'])).
% 0.52/0.76  thf('60', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.52/0.76            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 0.52/0.76          | (r2_hidden @ X0 @ X1))),
% 0.52/0.76      inference('sup+', [status(thm)], ['56', '59'])).
% 0.52/0.76  thf('61', plain,
% 0.52/0.76      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.76  thf('62', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['28', '29'])).
% 0.52/0.76  thf('63', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.52/0.76          | (r2_hidden @ X0 @ X1))),
% 0.52/0.76      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.52/0.76  thf('64', plain,
% 0.52/0.76      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 0.52/0.76         <= (~
% 0.52/0.76             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.76      inference('split', [status(esa)], ['3'])).
% 0.52/0.76  thf('65', plain,
% 0.52/0.76      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.52/0.76       ((r2_hidden @ sk_A @ sk_B_1))),
% 0.52/0.76      inference('split', [status(esa)], ['3'])).
% 0.52/0.76  thf('66', plain,
% 0.52/0.76      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.52/0.76      inference('sat_resolution*', [status(thm)], ['2', '45', '65'])).
% 0.52/0.76  thf('67', plain,
% 0.52/0.76      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A))),
% 0.52/0.76      inference('simpl_trail', [status(thm)], ['64', '66'])).
% 0.52/0.76  thf('68', plain,
% 0.52/0.76      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.52/0.76        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.52/0.76      inference('sup-', [status(thm)], ['63', '67'])).
% 0.52/0.76  thf('69', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.52/0.76      inference('simplify', [status(thm)], ['68'])).
% 0.52/0.76  thf('70', plain, ($false), inference('demod', [status(thm)], ['47', '69'])).
% 0.52/0.76  
% 0.52/0.76  % SZS output end Refutation
% 0.52/0.76  
% 0.62/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
