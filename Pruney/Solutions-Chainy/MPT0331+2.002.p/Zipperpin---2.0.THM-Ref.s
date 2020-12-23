%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.f1WFvKfvdx

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:03 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 538 expanded)
%              Number of leaves         :   24 ( 191 expanded)
%              Depth                    :   21
%              Number of atoms          :  620 (3920 expanded)
%              Number of equality atoms :   70 ( 519 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t144_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( r1_xboole_0 @ ( k2_tarski @ X23 @ X25 ) @ X24 )
      | ( r2_hidden @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_tarski @ X18 @ X17 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','22','25'])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','42'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','47','48'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','41'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['0','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.f1WFvKfvdx
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:48 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.11  % Solved by: fo/fo7.sh
% 0.90/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.11  % done 969 iterations in 0.658s
% 0.90/1.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.11  % SZS output start Refutation
% 0.90/1.11  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.11  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.11  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.11  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.11  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.90/1.11  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.11  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.90/1.11  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(t144_zfmisc_1, conjecture,
% 0.90/1.11    (![A:$i,B:$i,C:$i]:
% 0.90/1.11     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.90/1.11          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.90/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.11    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.11        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.90/1.11             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.90/1.11    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 0.90/1.11  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf(t57_zfmisc_1, axiom,
% 0.90/1.11    (![A:$i,B:$i,C:$i]:
% 0.90/1.11     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.90/1.11          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.90/1.11  thf('1', plain,
% 0.90/1.11      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.90/1.11         ((r2_hidden @ X23 @ X24)
% 0.90/1.11          | (r1_xboole_0 @ (k2_tarski @ X23 @ X25) @ X24)
% 0.90/1.11          | (r2_hidden @ X25 @ X24))),
% 0.90/1.11      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 0.90/1.11  thf(t83_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.90/1.11  thf('2', plain,
% 0.90/1.11      (![X7 : $i, X8 : $i]:
% 0.90/1.11         (((k4_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_xboole_0 @ X7 @ X8))),
% 0.90/1.11      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.90/1.11  thf('3', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.11         ((r2_hidden @ X1 @ X0)
% 0.90/1.11          | (r2_hidden @ X2 @ X0)
% 0.90/1.11          | ((k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) = (k2_tarski @ X2 @ X1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.11  thf(commutativity_k2_tarski, axiom,
% 0.90/1.11    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.90/1.11  thf('4', plain,
% 0.90/1.11      (![X17 : $i, X18 : $i]:
% 0.90/1.11         ((k2_tarski @ X18 @ X17) = (k2_tarski @ X17 @ X18))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.90/1.11  thf(l51_zfmisc_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.90/1.11  thf('5', plain,
% 0.90/1.11      (![X21 : $i, X22 : $i]:
% 0.90/1.11         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 0.90/1.11      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.90/1.11  thf('6', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['4', '5'])).
% 0.90/1.11  thf('7', plain,
% 0.90/1.11      (![X21 : $i, X22 : $i]:
% 0.90/1.11         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 0.90/1.11      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.90/1.11  thf('8', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['6', '7'])).
% 0.90/1.11  thf('9', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['6', '7'])).
% 0.90/1.11  thf(t95_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( k3_xboole_0 @ A @ B ) =
% 0.90/1.11       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.90/1.11  thf('10', plain,
% 0.90/1.11      (![X15 : $i, X16 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ X15 @ X16)
% 0.90/1.11           = (k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ 
% 0.90/1.11              (k2_xboole_0 @ X15 @ X16)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.90/1.11  thf(commutativity_k5_xboole_0, axiom,
% 0.90/1.11    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.90/1.11  thf('11', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.90/1.11  thf('12', plain,
% 0.90/1.11      (![X15 : $i, X16 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ X15 @ X16)
% 0.90/1.11           = (k5_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 0.90/1.11              (k5_xboole_0 @ X15 @ X16)))),
% 0.90/1.11      inference('demod', [status(thm)], ['10', '11'])).
% 0.90/1.11  thf('13', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ X0 @ X1)
% 0.90/1.11           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['9', '12'])).
% 0.90/1.11  thf('14', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.90/1.11  thf(t2_boole, axiom,
% 0.90/1.11    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.90/1.11  thf('15', plain,
% 0.90/1.11      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.11      inference('cnf', [status(esa)], [t2_boole])).
% 0.90/1.11  thf(t93_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( k2_xboole_0 @ A @ B ) =
% 0.90/1.11       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.11  thf('16', plain,
% 0.90/1.11      (![X13 : $i, X14 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ X13 @ X14)
% 0.90/1.11           = (k2_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 0.90/1.11              (k3_xboole_0 @ X13 @ X14)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t93_xboole_1])).
% 0.90/1.11  thf('17', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['6', '7'])).
% 0.90/1.11  thf('18', plain,
% 0.90/1.11      (![X13 : $i, X14 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ X13 @ X14)
% 0.90/1.11           = (k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ 
% 0.90/1.11              (k5_xboole_0 @ X13 @ X14)))),
% 0.90/1.11      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.11  thf('19', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.90/1.11           = (k2_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['15', '18'])).
% 0.90/1.11  thf('20', plain,
% 0.90/1.11      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.11      inference('cnf', [status(esa)], [t2_boole])).
% 0.90/1.11  thf(t22_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.90/1.11  thf('21', plain,
% 0.90/1.11      (![X4 : $i, X5 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)) = (X4))),
% 0.90/1.11      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.90/1.11  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['20', '21'])).
% 0.90/1.11  thf('23', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['6', '7'])).
% 0.90/1.11  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['20', '21'])).
% 0.90/1.11  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['23', '24'])).
% 0.90/1.11  thf('26', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.11      inference('demod', [status(thm)], ['19', '22', '25'])).
% 0.90/1.11  thf('27', plain,
% 0.90/1.11      (![X15 : $i, X16 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ X15 @ X16)
% 0.90/1.11           = (k5_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 0.90/1.11              (k5_xboole_0 @ X15 @ X16)))),
% 0.90/1.11      inference('demod', [status(thm)], ['10', '11'])).
% 0.90/1.11  thf('28', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.90/1.11           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['26', '27'])).
% 0.90/1.11  thf('29', plain,
% 0.90/1.11      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.11      inference('cnf', [status(esa)], [t2_boole])).
% 0.90/1.11  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['20', '21'])).
% 0.90/1.11  thf('31', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.90/1.11  thf(t91_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i,C:$i]:
% 0.90/1.11     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.90/1.11       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.90/1.11  thf('32', plain,
% 0.90/1.11      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.90/1.11           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.90/1.11  thf('33', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.90/1.11           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['31', '32'])).
% 0.90/1.11  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['23', '24'])).
% 0.90/1.11  thf('35', plain,
% 0.90/1.11      (![X4 : $i, X5 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)) = (X4))),
% 0.90/1.11      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.90/1.11  thf('36', plain,
% 0.90/1.11      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['34', '35'])).
% 0.90/1.11  thf('37', plain,
% 0.90/1.11      (![X13 : $i, X14 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ X13 @ X14)
% 0.90/1.11           = (k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ 
% 0.90/1.11              (k5_xboole_0 @ X13 @ X14)))),
% 0.90/1.11      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.11  thf('38', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.90/1.11           = (k2_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['36', '37'])).
% 0.90/1.11  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['23', '24'])).
% 0.90/1.11  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['23', '24'])).
% 0.90/1.11  thf('41', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.90/1.11  thf('42', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['33', '41'])).
% 0.90/1.11  thf('43', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['14', '42'])).
% 0.90/1.11  thf('44', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ X0 @ X1)
% 0.90/1.11           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['13', '43'])).
% 0.90/1.11  thf('45', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.90/1.11  thf('46', plain,
% 0.90/1.11      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.90/1.11           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.90/1.11  thf('47', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.90/1.11           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['45', '46'])).
% 0.90/1.11  thf(t100_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.11  thf('48', plain,
% 0.90/1.11      (![X2 : $i, X3 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X2 @ X3)
% 0.90/1.11           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.11  thf('49', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ X0 @ X1)
% 0.90/1.11           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['44', '47', '48'])).
% 0.90/1.11  thf('50', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['14', '42'])).
% 0.90/1.11  thf('51', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((X1)
% 0.90/1.11           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['49', '50'])).
% 0.90/1.11  thf('52', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((X0)
% 0.90/1.11           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['8', '51'])).
% 0.90/1.11  thf('53', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.11         (((X2)
% 0.90/1.11            = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 0.90/1.11               (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))
% 0.90/1.11          | (r2_hidden @ X1 @ X2)
% 0.90/1.11          | (r2_hidden @ X0 @ X2))),
% 0.90/1.11      inference('sup+', [status(thm)], ['3', '52'])).
% 0.90/1.11  thf('54', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ X0 @ X1)
% 0.90/1.11           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['44', '47', '48'])).
% 0.90/1.11  thf('55', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['33', '41'])).
% 0.90/1.11  thf('56', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X0 @ X1)
% 0.90/1.11           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['54', '55'])).
% 0.90/1.11  thf('57', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.11         (((X2) = (k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))
% 0.90/1.11          | (r2_hidden @ X1 @ X2)
% 0.90/1.11          | (r2_hidden @ X0 @ X2))),
% 0.90/1.11      inference('demod', [status(thm)], ['53', '56'])).
% 0.90/1.11  thf('58', plain,
% 0.90/1.11      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('59', plain,
% 0.90/1.11      ((((sk_C) != (sk_C))
% 0.90/1.11        | (r2_hidden @ sk_B @ sk_C)
% 0.90/1.11        | (r2_hidden @ sk_A @ sk_C))),
% 0.90/1.11      inference('sup-', [status(thm)], ['57', '58'])).
% 0.90/1.11  thf('60', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 0.90/1.11      inference('simplify', [status(thm)], ['59'])).
% 0.90/1.11  thf('61', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('62', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.90/1.11      inference('clc', [status(thm)], ['60', '61'])).
% 0.90/1.11  thf('63', plain, ($false), inference('demod', [status(thm)], ['0', '62'])).
% 0.90/1.11  
% 0.90/1.11  % SZS output end Refutation
% 0.90/1.11  
% 0.90/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
