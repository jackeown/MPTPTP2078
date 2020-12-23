%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c78wwLfvVm

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:22 EST 2020

% Result     : Theorem 4.79s
% Output     : Refutation 4.79s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 163 expanded)
%              Number of leaves         :   24 (  59 expanded)
%              Depth                    :   26
%              Number of atoms          :  782 (1297 expanded)
%              Number of equality atoms :   54 (  83 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k4_xboole_0 @ X35 @ ( k1_tarski @ X36 ) )
        = X35 )
      | ( r2_hidden @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_xboole_0 @ X21 @ X23 )
      | ( ( k4_xboole_0 @ X21 @ X23 )
       != X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != ( k4_xboole_0 @ X2 @ X1 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','15'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('28',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('35',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,(
    r1_tarski @ sk_C_1 @ sk_C_1 ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != ( k4_xboole_0 @ X2 @ X1 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ sk_C_1 )
       != ( k4_xboole_0 @ X0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ sk_D @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ sk_D @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['23','55'])).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ) @ X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('63',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('64',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('69',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('71',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != ( k4_xboole_0 @ X2 @ X1 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) )
       != ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['64','74'])).

thf('76',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('81',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_xboole_0 @ X21 @ X23 )
      | ( ( k4_xboole_0 @ X21 @ X23 )
       != X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
       != sk_B )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B != sk_B )
    | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('86',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['2','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c78wwLfvVm
% 0.13/0.36  % Computer   : n015.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 14:02:38 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.22/0.37  % Running in FO mode
% 4.79/5.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.79/5.04  % Solved by: fo/fo7.sh
% 4.79/5.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.79/5.04  % done 7967 iterations in 4.562s
% 4.79/5.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.79/5.04  % SZS output start Refutation
% 4.79/5.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.79/5.04  thf(sk_D_type, type, sk_D: $i).
% 4.79/5.04  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.79/5.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.79/5.04  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.79/5.04  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.79/5.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.79/5.04  thf(sk_A_type, type, sk_A: $i).
% 4.79/5.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.79/5.04  thf(sk_B_type, type, sk_B: $i).
% 4.79/5.04  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.79/5.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.79/5.04  thf(t149_zfmisc_1, conjecture,
% 4.79/5.04    (![A:$i,B:$i,C:$i,D:$i]:
% 4.79/5.04     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 4.79/5.04         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 4.79/5.04       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 4.79/5.04  thf(zf_stmt_0, negated_conjecture,
% 4.79/5.04    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.79/5.04        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 4.79/5.04            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 4.79/5.04          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 4.79/5.04    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 4.79/5.04  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 4.79/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.79/5.04  thf(commutativity_k2_xboole_0, axiom,
% 4.79/5.04    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.79/5.04  thf('1', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.79/5.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.79/5.04  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 4.79/5.04      inference('demod', [status(thm)], ['0', '1'])).
% 4.79/5.04  thf(t65_zfmisc_1, axiom,
% 4.79/5.04    (![A:$i,B:$i]:
% 4.79/5.04     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 4.79/5.04       ( ~( r2_hidden @ B @ A ) ) ))).
% 4.79/5.04  thf('3', plain,
% 4.79/5.04      (![X35 : $i, X36 : $i]:
% 4.79/5.04         (((k4_xboole_0 @ X35 @ (k1_tarski @ X36)) = (X35))
% 4.79/5.04          | (r2_hidden @ X36 @ X35))),
% 4.79/5.04      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 4.79/5.04  thf(t48_xboole_1, axiom,
% 4.79/5.04    (![A:$i,B:$i]:
% 4.79/5.04     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.79/5.04  thf('4', plain,
% 4.79/5.04      (![X19 : $i, X20 : $i]:
% 4.79/5.04         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 4.79/5.04           = (k3_xboole_0 @ X19 @ X20))),
% 4.79/5.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.79/5.04  thf(t36_xboole_1, axiom,
% 4.79/5.04    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.79/5.04  thf('5', plain,
% 4.79/5.04      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 4.79/5.04      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.79/5.04  thf(t12_xboole_1, axiom,
% 4.79/5.04    (![A:$i,B:$i]:
% 4.79/5.04     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 4.79/5.04  thf('6', plain,
% 4.79/5.04      (![X10 : $i, X11 : $i]:
% 4.79/5.04         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 4.79/5.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.79/5.04  thf('7', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i]:
% 4.79/5.04         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 4.79/5.04      inference('sup-', [status(thm)], ['5', '6'])).
% 4.79/5.04  thf('8', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.79/5.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.79/5.04  thf('9', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i]:
% 4.79/5.04         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 4.79/5.04      inference('demod', [status(thm)], ['7', '8'])).
% 4.79/5.04  thf('10', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i]:
% 4.79/5.04         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 4.79/5.04      inference('sup+', [status(thm)], ['4', '9'])).
% 4.79/5.04  thf(t41_xboole_1, axiom,
% 4.79/5.04    (![A:$i,B:$i,C:$i]:
% 4.79/5.04     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 4.79/5.04       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 4.79/5.04  thf('11', plain,
% 4.79/5.04      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.79/5.04         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 4.79/5.04           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 4.79/5.04      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.79/5.04  thf(t83_xboole_1, axiom,
% 4.79/5.04    (![A:$i,B:$i]:
% 4.79/5.04     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.79/5.04  thf('12', plain,
% 4.79/5.04      (![X21 : $i, X23 : $i]:
% 4.79/5.04         ((r1_xboole_0 @ X21 @ X23) | ((k4_xboole_0 @ X21 @ X23) != (X21)))),
% 4.79/5.04      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.79/5.04  thf('13', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.79/5.04         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 4.79/5.04            != (k4_xboole_0 @ X2 @ X1))
% 4.79/5.04          | (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 4.79/5.04      inference('sup-', [status(thm)], ['11', '12'])).
% 4.79/5.04  thf('14', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.79/5.04         (((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X1 @ X0))
% 4.79/5.04          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2)))),
% 4.79/5.04      inference('sup-', [status(thm)], ['10', '13'])).
% 4.79/5.04  thf('15', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.79/5.04         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2))),
% 4.79/5.04      inference('simplify', [status(thm)], ['14'])).
% 4.79/5.04  thf('16', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.79/5.04         ((r1_xboole_0 @ X0 @ (k3_xboole_0 @ (k1_tarski @ X2) @ X1))
% 4.79/5.04          | (r2_hidden @ X2 @ X0))),
% 4.79/5.04      inference('sup+', [status(thm)], ['3', '15'])).
% 4.79/5.04  thf(t3_xboole_0, axiom,
% 4.79/5.04    (![A:$i,B:$i]:
% 4.79/5.04     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 4.79/5.04            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.79/5.04       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.79/5.04            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 4.79/5.04  thf('17', plain,
% 4.79/5.04      (![X6 : $i, X7 : $i]:
% 4.79/5.04         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 4.79/5.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.79/5.04  thf('18', plain,
% 4.79/5.04      (![X6 : $i, X7 : $i]:
% 4.79/5.04         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 4.79/5.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.79/5.04  thf('19', plain,
% 4.79/5.04      (![X6 : $i, X8 : $i, X9 : $i]:
% 4.79/5.04         (~ (r2_hidden @ X8 @ X6)
% 4.79/5.04          | ~ (r2_hidden @ X8 @ X9)
% 4.79/5.04          | ~ (r1_xboole_0 @ X6 @ X9))),
% 4.79/5.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.79/5.04  thf('20', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.79/5.04         ((r1_xboole_0 @ X0 @ X1)
% 4.79/5.04          | ~ (r1_xboole_0 @ X0 @ X2)
% 4.79/5.04          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 4.79/5.04      inference('sup-', [status(thm)], ['18', '19'])).
% 4.79/5.04  thf('21', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i]:
% 4.79/5.04         ((r1_xboole_0 @ X0 @ X1)
% 4.79/5.04          | ~ (r1_xboole_0 @ X0 @ X0)
% 4.79/5.04          | (r1_xboole_0 @ X0 @ X1))),
% 4.79/5.04      inference('sup-', [status(thm)], ['17', '20'])).
% 4.79/5.04  thf('22', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i]:
% 4.79/5.04         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 4.79/5.04      inference('simplify', [status(thm)], ['21'])).
% 4.79/5.04  thf('23', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.79/5.04         ((r2_hidden @ X1 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 4.79/5.04          | (r1_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0) @ X2))),
% 4.79/5.04      inference('sup-', [status(thm)], ['16', '22'])).
% 4.79/5.04  thf(commutativity_k3_xboole_0, axiom,
% 4.79/5.04    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.79/5.04  thf('24', plain,
% 4.79/5.04      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.79/5.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.79/5.04  thf('25', plain,
% 4.79/5.04      (![X19 : $i, X20 : $i]:
% 4.79/5.04         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 4.79/5.04           = (k3_xboole_0 @ X19 @ X20))),
% 4.79/5.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.79/5.04  thf('26', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 4.79/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.79/5.04  thf(symmetry_r1_xboole_0, axiom,
% 4.79/5.04    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 4.79/5.04  thf('27', plain,
% 4.79/5.04      (![X4 : $i, X5 : $i]:
% 4.79/5.04         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 4.79/5.04      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.79/5.04  thf('28', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 4.79/5.04      inference('sup-', [status(thm)], ['26', '27'])).
% 4.79/5.04  thf('29', plain,
% 4.79/5.04      (![X21 : $i, X22 : $i]:
% 4.79/5.04         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 4.79/5.04      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.79/5.04  thf('30', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 4.79/5.04      inference('sup-', [status(thm)], ['28', '29'])).
% 4.79/5.04  thf('31', plain,
% 4.79/5.04      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.79/5.04         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 4.79/5.04           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 4.79/5.04      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.79/5.04  thf('32', plain,
% 4.79/5.04      (![X0 : $i]:
% 4.79/5.04         ((k4_xboole_0 @ sk_B @ X0)
% 4.79/5.04           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 4.79/5.04      inference('sup+', [status(thm)], ['30', '31'])).
% 4.79/5.04  thf('33', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.79/5.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.79/5.04  thf('34', plain,
% 4.79/5.04      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.79/5.04         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 4.79/5.04           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 4.79/5.04      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.79/5.04  thf('35', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 4.79/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.79/5.04  thf('36', plain,
% 4.79/5.04      (![X21 : $i, X22 : $i]:
% 4.79/5.04         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 4.79/5.04      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.79/5.04  thf('37', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 4.79/5.04      inference('sup-', [status(thm)], ['35', '36'])).
% 4.79/5.04  thf('38', plain,
% 4.79/5.04      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 4.79/5.04      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.79/5.04  thf('39', plain, ((r1_tarski @ sk_C_1 @ sk_C_1)),
% 4.79/5.04      inference('sup+', [status(thm)], ['37', '38'])).
% 4.79/5.04  thf('40', plain,
% 4.79/5.04      (![X10 : $i, X11 : $i]:
% 4.79/5.04         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 4.79/5.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.79/5.04  thf('41', plain, (((k2_xboole_0 @ sk_C_1 @ sk_C_1) = (sk_C_1))),
% 4.79/5.04      inference('sup-', [status(thm)], ['39', '40'])).
% 4.79/5.04  thf('42', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.79/5.04         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 4.79/5.04            != (k4_xboole_0 @ X2 @ X1))
% 4.79/5.04          | (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 4.79/5.04      inference('sup-', [status(thm)], ['11', '12'])).
% 4.79/5.04  thf('43', plain,
% 4.79/5.04      (![X0 : $i]:
% 4.79/5.04         (((k4_xboole_0 @ X0 @ sk_C_1) != (k4_xboole_0 @ X0 @ sk_C_1))
% 4.79/5.04          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_C_1))),
% 4.79/5.04      inference('sup-', [status(thm)], ['41', '42'])).
% 4.79/5.04  thf('44', plain,
% 4.79/5.04      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_C_1)),
% 4.79/5.04      inference('simplify', [status(thm)], ['43'])).
% 4.79/5.04  thf('45', plain,
% 4.79/5.04      (![X4 : $i, X5 : $i]:
% 4.79/5.04         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 4.79/5.04      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.79/5.04  thf('46', plain,
% 4.79/5.04      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ X0 @ sk_C_1))),
% 4.79/5.04      inference('sup-', [status(thm)], ['44', '45'])).
% 4.79/5.04  thf('47', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 4.79/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.79/5.04  thf('48', plain,
% 4.79/5.04      (![X6 : $i, X8 : $i, X9 : $i]:
% 4.79/5.04         (~ (r2_hidden @ X8 @ X6)
% 4.79/5.04          | ~ (r2_hidden @ X8 @ X9)
% 4.79/5.04          | ~ (r1_xboole_0 @ X6 @ X9))),
% 4.79/5.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.79/5.04  thf('49', plain,
% 4.79/5.04      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 4.79/5.04      inference('sup-', [status(thm)], ['47', '48'])).
% 4.79/5.04  thf('50', plain,
% 4.79/5.04      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k4_xboole_0 @ X0 @ sk_C_1))),
% 4.79/5.04      inference('sup-', [status(thm)], ['46', '49'])).
% 4.79/5.04  thf('51', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i]:
% 4.79/5.04         ~ (r2_hidden @ sk_D @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ sk_C_1)))),
% 4.79/5.04      inference('sup-', [status(thm)], ['34', '50'])).
% 4.79/5.04  thf('52', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i]:
% 4.79/5.04         ~ (r2_hidden @ sk_D @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 4.79/5.04      inference('sup-', [status(thm)], ['33', '51'])).
% 4.79/5.04  thf('53', plain,
% 4.79/5.04      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k4_xboole_0 @ sk_B @ X0))),
% 4.79/5.04      inference('sup-', [status(thm)], ['32', '52'])).
% 4.79/5.04  thf('54', plain,
% 4.79/5.04      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 4.79/5.04      inference('sup-', [status(thm)], ['25', '53'])).
% 4.79/5.04  thf('55', plain,
% 4.79/5.04      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ X0 @ sk_B))),
% 4.79/5.04      inference('sup-', [status(thm)], ['24', '54'])).
% 4.79/5.04  thf('56', plain,
% 4.79/5.04      (![X0 : $i]:
% 4.79/5.04         (r1_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) @ X0)),
% 4.79/5.04      inference('sup-', [status(thm)], ['23', '55'])).
% 4.79/5.04  thf('57', plain,
% 4.79/5.04      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.79/5.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.79/5.04  thf('58', plain,
% 4.79/5.04      (![X0 : $i]:
% 4.79/5.04         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) @ X0)),
% 4.79/5.04      inference('demod', [status(thm)], ['56', '57'])).
% 4.79/5.04  thf('59', plain,
% 4.79/5.04      (![X4 : $i, X5 : $i]:
% 4.79/5.04         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 4.79/5.04      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.79/5.04  thf('60', plain,
% 4.79/5.04      (![X0 : $i]:
% 4.79/5.04         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)))),
% 4.79/5.04      inference('sup-', [status(thm)], ['58', '59'])).
% 4.79/5.04  thf('61', plain,
% 4.79/5.04      (![X21 : $i, X22 : $i]:
% 4.79/5.04         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 4.79/5.04      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.79/5.04  thf('62', plain,
% 4.79/5.04      (![X0 : $i]:
% 4.79/5.04         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D))) = (X0))),
% 4.79/5.04      inference('sup-', [status(thm)], ['60', '61'])).
% 4.79/5.04  thf(t47_xboole_1, axiom,
% 4.79/5.04    (![A:$i,B:$i]:
% 4.79/5.04     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.79/5.04  thf('63', plain,
% 4.79/5.04      (![X17 : $i, X18 : $i]:
% 4.79/5.04         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 4.79/5.04           = (k4_xboole_0 @ X17 @ X18))),
% 4.79/5.04      inference('cnf', [status(esa)], [t47_xboole_1])).
% 4.79/5.04  thf('64', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D)))),
% 4.79/5.04      inference('sup+', [status(thm)], ['62', '63'])).
% 4.79/5.04  thf('65', plain,
% 4.79/5.04      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 4.79/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.79/5.04  thf('66', plain,
% 4.79/5.04      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.79/5.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.79/5.04  thf('67', plain,
% 4.79/5.04      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 4.79/5.04      inference('demod', [status(thm)], ['65', '66'])).
% 4.79/5.04  thf('68', plain,
% 4.79/5.04      (![X10 : $i, X11 : $i]:
% 4.79/5.04         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 4.79/5.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.79/5.04  thf('69', plain,
% 4.79/5.04      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 4.79/5.04         = (k1_tarski @ sk_D))),
% 4.79/5.04      inference('sup-', [status(thm)], ['67', '68'])).
% 4.79/5.04  thf('70', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.79/5.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.79/5.04  thf('71', plain,
% 4.79/5.04      (((k2_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 4.79/5.04         = (k1_tarski @ sk_D))),
% 4.79/5.04      inference('demod', [status(thm)], ['69', '70'])).
% 4.79/5.04  thf('72', plain,
% 4.79/5.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.79/5.04         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 4.79/5.04            != (k4_xboole_0 @ X2 @ X1))
% 4.79/5.04          | (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 4.79/5.04      inference('sup-', [status(thm)], ['11', '12'])).
% 4.79/5.04  thf('73', plain,
% 4.79/5.04      (![X0 : $i]:
% 4.79/5.04         (((k4_xboole_0 @ X0 @ (k1_tarski @ sk_D))
% 4.79/5.04            != (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D)))
% 4.79/5.04          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D)) @ 
% 4.79/5.04             (k3_xboole_0 @ sk_B @ sk_A)))),
% 4.79/5.04      inference('sup-', [status(thm)], ['71', '72'])).
% 4.79/5.04  thf('74', plain,
% 4.79/5.04      (![X0 : $i]:
% 4.79/5.04         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D)) @ 
% 4.79/5.04          (k3_xboole_0 @ sk_B @ sk_A))),
% 4.79/5.04      inference('simplify', [status(thm)], ['73'])).
% 4.79/5.04  thf('75', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 4.79/5.04      inference('sup+', [status(thm)], ['64', '74'])).
% 4.79/5.04  thf('76', plain,
% 4.79/5.04      (![X21 : $i, X22 : $i]:
% 4.79/5.04         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 4.79/5.04      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.79/5.04  thf('77', plain,
% 4.79/5.04      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 4.79/5.04      inference('sup-', [status(thm)], ['75', '76'])).
% 4.79/5.04  thf('78', plain,
% 4.79/5.04      (![X17 : $i, X18 : $i]:
% 4.79/5.04         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 4.79/5.04           = (k4_xboole_0 @ X17 @ X18))),
% 4.79/5.04      inference('cnf', [status(esa)], [t47_xboole_1])).
% 4.79/5.04  thf('79', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 4.79/5.04      inference('demod', [status(thm)], ['77', '78'])).
% 4.79/5.04  thf('80', plain,
% 4.79/5.04      (![X0 : $i]:
% 4.79/5.04         ((k4_xboole_0 @ sk_B @ X0)
% 4.79/5.04           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 4.79/5.04      inference('sup+', [status(thm)], ['30', '31'])).
% 4.79/5.04  thf('81', plain,
% 4.79/5.04      (![X21 : $i, X23 : $i]:
% 4.79/5.04         ((r1_xboole_0 @ X21 @ X23) | ((k4_xboole_0 @ X21 @ X23) != (X21)))),
% 4.79/5.04      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.79/5.04  thf('82', plain,
% 4.79/5.04      (![X0 : $i]:
% 4.79/5.04         (((k4_xboole_0 @ sk_B @ X0) != (sk_B))
% 4.79/5.04          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 4.79/5.04      inference('sup-', [status(thm)], ['80', '81'])).
% 4.79/5.04  thf('83', plain,
% 4.79/5.04      ((((sk_B) != (sk_B))
% 4.79/5.04        | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 4.79/5.04      inference('sup-', [status(thm)], ['79', '82'])).
% 4.79/5.04  thf('84', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 4.79/5.04      inference('simplify', [status(thm)], ['83'])).
% 4.79/5.04  thf('85', plain,
% 4.79/5.04      (![X4 : $i, X5 : $i]:
% 4.79/5.04         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 4.79/5.04      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.79/5.04  thf('86', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 4.79/5.04      inference('sup-', [status(thm)], ['84', '85'])).
% 4.79/5.04  thf('87', plain, ($false), inference('demod', [status(thm)], ['2', '86'])).
% 4.79/5.04  
% 4.79/5.04  % SZS output end Refutation
% 4.79/5.04  
% 4.79/5.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
