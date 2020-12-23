%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7IuAtEEMCP

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:03 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  151 (1135 expanded)
%              Number of leaves         :   23 ( 387 expanded)
%              Depth                    :   15
%              Number of atoms          : 1033 (9806 expanded)
%              Number of equality atoms :  114 ( 943 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_2 @ sk_D ) ),
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

thf('2',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference('sup-',[status(thm)],['5','11'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_2 ) @ sk_D )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_2 ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('50',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('54',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('55',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('64',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','64'])).

thf('66',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('67',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','65','66','67'])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','68'])).

thf('70',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('71',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_D @ sk_A ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('75',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('76',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('77',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_C_2 @ sk_D ) )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('80',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ sk_D )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('82',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('84',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','64'])).

thf('86',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('87',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('91',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('93',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86','93'])).

thf('95',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('96',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('98',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('100',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','68'])).

thf('101',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('102',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['73','74','98','99','100','101'])).

thf('103',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('104',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['73','74','98','99','100','101'])).

thf('105',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('107',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('109',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('111',plain,
    ( sk_C_2
    = ( k4_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_2 ),
    inference(demod,[status(thm)],['4','102','103','104','111'])).

thf('113',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('115',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_D ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('117',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('119',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('121',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['73','74','98','99','100','101'])).

thf('123',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    sk_B_1 = sk_C_2 ),
    inference('sup+',[status(thm)],['112','123'])).

thf('125',plain,(
    sk_C_2 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['124','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7IuAtEEMCP
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:32:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.58/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.80  % Solved by: fo/fo7.sh
% 0.58/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.80  % done 458 iterations in 0.334s
% 0.58/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.80  % SZS output start Refutation
% 0.58/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.80  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.80  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.58/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.80  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.80  thf(t72_xboole_1, conjecture,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.58/0.80         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.58/0.80       ( ( C ) = ( B ) ) ))).
% 0.58/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.80    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.58/0.80            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.58/0.80          ( ( C ) = ( B ) ) ) )),
% 0.58/0.80    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.58/0.80  thf('0', plain,
% 0.58/0.80      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_2 @ sk_D))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(commutativity_k2_xboole_0, axiom,
% 0.58/0.80    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.58/0.80  thf('1', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.80  thf('2', plain,
% 0.58/0.80      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_2 @ sk_D))),
% 0.58/0.80      inference('demod', [status(thm)], ['0', '1'])).
% 0.58/0.80  thf(t40_xboole_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.58/0.80  thf('3', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.58/0.80           = (k4_xboole_0 @ X16 @ X17))),
% 0.58/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.80  thf('4', plain,
% 0.58/0.80      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D)
% 0.58/0.80         = (k4_xboole_0 @ sk_C_2 @ sk_D))),
% 0.58/0.80      inference('sup+', [status(thm)], ['2', '3'])).
% 0.58/0.80  thf('5', plain, ((r1_xboole_0 @ sk_C_2 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(t3_xboole_0, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.58/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.58/0.80            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.58/0.80  thf('6', plain,
% 0.58/0.80      (![X3 : $i, X4 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.80  thf('7', plain,
% 0.58/0.80      (![X3 : $i, X4 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.80  thf('8', plain,
% 0.58/0.80      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X5 @ X3)
% 0.58/0.80          | ~ (r2_hidden @ X5 @ X6)
% 0.58/0.80          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.80  thf('9', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X1 @ X0)
% 0.58/0.80          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.58/0.80          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.80  thf('10', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X0 @ X1)
% 0.58/0.80          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.58/0.80          | (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['6', '9'])).
% 0.58/0.80  thf('11', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.80      inference('simplify', [status(thm)], ['10'])).
% 0.58/0.80  thf('12', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 0.58/0.80      inference('sup-', [status(thm)], ['5', '11'])).
% 0.58/0.80  thf(t7_xboole_0, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.58/0.80          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.58/0.80  thf('13', plain,
% 0.58/0.80      (![X11 : $i]:
% 0.58/0.80         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.58/0.80      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.80  thf(t4_xboole_0, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.58/0.80            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.58/0.80  thf('14', plain,
% 0.58/0.80      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.58/0.80          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.58/0.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.80  thf('15', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.80  thf('16', plain, (((k3_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['12', '15'])).
% 0.58/0.80  thf(t47_xboole_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.58/0.80  thf('17', plain,
% 0.58/0.80      (![X21 : $i, X22 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22))
% 0.58/0.80           = (k4_xboole_0 @ X21 @ X22))),
% 0.58/0.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.58/0.80  thf('18', plain,
% 0.58/0.80      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 0.58/0.80      inference('sup+', [status(thm)], ['16', '17'])).
% 0.58/0.80  thf(t3_boole, axiom,
% 0.58/0.80    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.80  thf('19', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.80  thf('20', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 0.58/0.80      inference('demod', [status(thm)], ['18', '19'])).
% 0.58/0.80  thf('21', plain,
% 0.58/0.80      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_2 @ sk_D))),
% 0.58/0.80      inference('demod', [status(thm)], ['0', '1'])).
% 0.58/0.80  thf(t41_xboole_1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.58/0.80       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.58/0.80  thf('22', plain,
% 0.58/0.80      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 0.58/0.80           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.58/0.80  thf('23', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_2) @ sk_D)
% 0.58/0.80           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['21', '22'])).
% 0.58/0.80  thf('24', plain,
% 0.58/0.80      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 0.58/0.80           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.58/0.80  thf('25', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_2) @ sk_D)
% 0.58/0.80           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B_1) @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['23', '24'])).
% 0.58/0.80  thf('26', plain,
% 0.58/0.80      (((k4_xboole_0 @ sk_A @ sk_D)
% 0.58/0.80         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ sk_A))),
% 0.58/0.80      inference('sup+', [status(thm)], ['20', '25'])).
% 0.58/0.80  thf('27', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.58/0.80           = (k4_xboole_0 @ X16 @ X17))),
% 0.58/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.80  thf(t39_xboole_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.80  thf('28', plain,
% 0.58/0.80      (![X13 : $i, X14 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.58/0.80           = (k2_xboole_0 @ X13 @ X14))),
% 0.58/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.58/0.80  thf('29', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.58/0.80           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['27', '28'])).
% 0.58/0.80  thf('30', plain,
% 0.58/0.80      (![X13 : $i, X14 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.58/0.80           = (k2_xboole_0 @ X13 @ X14))),
% 0.58/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.58/0.80  thf('31', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X0 @ X1)
% 0.58/0.80           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('demod', [status(thm)], ['29', '30'])).
% 0.58/0.80  thf('32', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X0 @ X1)
% 0.58/0.80           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('demod', [status(thm)], ['29', '30'])).
% 0.58/0.80  thf('33', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1)
% 0.58/0.80           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['31', '32'])).
% 0.58/0.80  thf('34', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.80  thf('35', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X0 @ X1)
% 0.58/0.80           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('demod', [status(thm)], ['29', '30'])).
% 0.58/0.80  thf('36', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X1 @ X0)
% 0.58/0.80           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.58/0.80  thf('37', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.58/0.80           = (k4_xboole_0 @ X16 @ X17))),
% 0.58/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.80  thf('38', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.58/0.80           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['36', '37'])).
% 0.58/0.80  thf('39', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.80  thf('40', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.58/0.80           = (k4_xboole_0 @ X16 @ X17))),
% 0.58/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.80  thf('41', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['39', '40'])).
% 0.58/0.80  thf('42', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.80  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['41', '42'])).
% 0.58/0.80  thf('44', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.80  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['43', '44'])).
% 0.58/0.80  thf('46', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.58/0.80           = (k4_xboole_0 @ X16 @ X17))),
% 0.58/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.80  thf('47', plain,
% 0.58/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['45', '46'])).
% 0.58/0.80  thf('48', plain, ((r1_xboole_0 @ sk_C_2 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('49', plain,
% 0.58/0.80      (![X3 : $i, X4 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.80  thf('50', plain,
% 0.58/0.80      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.58/0.80          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.58/0.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.80  thf('51', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.58/0.80          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['49', '50'])).
% 0.58/0.80  thf('52', plain,
% 0.58/0.80      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_A) @ X0)),
% 0.58/0.80      inference('sup-', [status(thm)], ['48', '51'])).
% 0.58/0.80  thf('53', plain,
% 0.58/0.80      (![X3 : $i, X4 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.80  thf(t2_boole, axiom,
% 0.58/0.80    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.58/0.80  thf('54', plain,
% 0.58/0.80      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.80      inference('cnf', [status(esa)], [t2_boole])).
% 0.58/0.80  thf('55', plain,
% 0.58/0.80      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.58/0.80          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.58/0.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.80  thf('56', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['54', '55'])).
% 0.58/0.80  thf('57', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['53', '56'])).
% 0.58/0.80  thf('58', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.58/0.80      inference('sup-', [status(thm)], ['52', '57'])).
% 0.58/0.80  thf('59', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.80  thf('60', plain,
% 0.58/0.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['58', '59'])).
% 0.58/0.80  thf('61', plain,
% 0.58/0.80      (![X21 : $i, X22 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22))
% 0.58/0.80           = (k4_xboole_0 @ X21 @ X22))),
% 0.58/0.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.58/0.80  thf('62', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.58/0.80           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['60', '61'])).
% 0.58/0.80  thf('63', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.80  thf('64', plain,
% 0.58/0.80      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['62', '63'])).
% 0.58/0.80  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.80      inference('demod', [status(thm)], ['47', '64'])).
% 0.58/0.80  thf('66', plain,
% 0.58/0.80      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 0.58/0.80           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.58/0.80  thf('67', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.58/0.80           = (k4_xboole_0 @ X16 @ X17))),
% 0.58/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.80  thf('68', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['38', '65', '66', '67'])).
% 0.58/0.80  thf('69', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 0.58/0.80      inference('demod', [status(thm)], ['26', '68'])).
% 0.58/0.80  thf('70', plain,
% 0.58/0.80      (![X13 : $i, X14 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.58/0.80           = (k2_xboole_0 @ X13 @ X14))),
% 0.58/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.58/0.80  thf('71', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.58/0.80           = (k4_xboole_0 @ X16 @ X17))),
% 0.58/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.80  thf('72', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.58/0.80           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['70', '71'])).
% 0.58/0.80  thf('73', plain,
% 0.58/0.80      (((k4_xboole_0 @ (k2_xboole_0 @ sk_D @ sk_A) @ k1_xboole_0)
% 0.58/0.80         = (k4_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_A @ sk_D)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['69', '72'])).
% 0.58/0.80  thf('74', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.80  thf('75', plain,
% 0.58/0.80      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D)
% 0.58/0.80         = (k4_xboole_0 @ sk_C_2 @ sk_D))),
% 0.58/0.80      inference('sup+', [status(thm)], ['2', '3'])).
% 0.58/0.80  thf('76', plain,
% 0.58/0.80      (![X13 : $i, X14 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.58/0.80           = (k2_xboole_0 @ X13 @ X14))),
% 0.58/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.58/0.80  thf('77', plain,
% 0.58/0.80      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_C_2 @ sk_D))
% 0.58/0.80         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['75', '76'])).
% 0.58/0.80  thf('78', plain,
% 0.58/0.80      (![X13 : $i, X14 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.58/0.80           = (k2_xboole_0 @ X13 @ X14))),
% 0.58/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.58/0.80  thf('79', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.80  thf('80', plain,
% 0.58/0.80      (((k2_xboole_0 @ sk_C_2 @ sk_D)
% 0.58/0.80         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.58/0.80  thf('81', plain,
% 0.58/0.80      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_2 @ sk_D))),
% 0.58/0.80      inference('demod', [status(thm)], ['0', '1'])).
% 0.58/0.80  thf('82', plain,
% 0.58/0.80      (((k2_xboole_0 @ sk_B_1 @ sk_A)
% 0.58/0.80         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['80', '81'])).
% 0.58/0.80  thf('83', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.58/0.80           = (k4_xboole_0 @ X16 @ X17))),
% 0.58/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.80  thf('84', plain,
% 0.58/0.80      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ 
% 0.58/0.80         (k2_xboole_0 @ sk_B_1 @ sk_A))
% 0.58/0.80         = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['82', '83'])).
% 0.58/0.80  thf('85', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.80      inference('demod', [status(thm)], ['47', '64'])).
% 0.58/0.80  thf('86', plain,
% 0.58/0.80      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 0.58/0.80           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.58/0.80  thf('87', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('88', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.80  thf('89', plain, (((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['87', '88'])).
% 0.58/0.80  thf('90', plain,
% 0.58/0.80      (![X21 : $i, X22 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22))
% 0.58/0.80           = (k4_xboole_0 @ X21 @ X22))),
% 0.58/0.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.58/0.80  thf('91', plain,
% 0.58/0.80      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.58/0.80      inference('sup+', [status(thm)], ['89', '90'])).
% 0.58/0.80  thf('92', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.80  thf('93', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.58/0.80      inference('demod', [status(thm)], ['91', '92'])).
% 0.58/0.80  thf('94', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['84', '85', '86', '93'])).
% 0.58/0.80  thf('95', plain,
% 0.58/0.80      (![X13 : $i, X14 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.58/0.80           = (k2_xboole_0 @ X13 @ X14))),
% 0.58/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.58/0.80  thf('96', plain,
% 0.58/0.80      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.58/0.80      inference('sup+', [status(thm)], ['94', '95'])).
% 0.58/0.80  thf('97', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['41', '42'])).
% 0.58/0.80  thf('98', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.58/0.80      inference('demod', [status(thm)], ['96', '97'])).
% 0.58/0.80  thf('99', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.80  thf('100', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 0.58/0.80      inference('demod', [status(thm)], ['26', '68'])).
% 0.58/0.80  thf('101', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.80  thf('102', plain, (((sk_A) = (sk_D))),
% 0.58/0.80      inference('demod', [status(thm)], ['73', '74', '98', '99', '100', '101'])).
% 0.58/0.80  thf('103', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.58/0.80           = (k4_xboole_0 @ X16 @ X17))),
% 0.58/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.80  thf('104', plain, (((sk_A) = (sk_D))),
% 0.58/0.80      inference('demod', [status(thm)], ['73', '74', '98', '99', '100', '101'])).
% 0.58/0.80  thf('105', plain, ((r1_xboole_0 @ sk_C_2 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('106', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.80  thf('107', plain, (((k3_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['105', '106'])).
% 0.58/0.80  thf('108', plain,
% 0.58/0.80      (![X21 : $i, X22 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22))
% 0.58/0.80           = (k4_xboole_0 @ X21 @ X22))),
% 0.58/0.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.58/0.80  thf('109', plain,
% 0.58/0.80      (((k4_xboole_0 @ sk_C_2 @ k1_xboole_0) = (k4_xboole_0 @ sk_C_2 @ sk_A))),
% 0.58/0.80      inference('sup+', [status(thm)], ['107', '108'])).
% 0.58/0.80  thf('110', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.80  thf('111', plain, (((sk_C_2) = (k4_xboole_0 @ sk_C_2 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['109', '110'])).
% 0.58/0.80  thf('112', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_2))),
% 0.58/0.80      inference('demod', [status(thm)], ['4', '102', '103', '104', '111'])).
% 0.58/0.80  thf('113', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('114', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.80      inference('simplify', [status(thm)], ['10'])).
% 0.58/0.80  thf('115', plain, ((r1_xboole_0 @ sk_B_1 @ sk_D)),
% 0.58/0.80      inference('sup-', [status(thm)], ['113', '114'])).
% 0.58/0.80  thf('116', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.80  thf('117', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['115', '116'])).
% 0.58/0.80  thf('118', plain,
% 0.58/0.80      (![X21 : $i, X22 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22))
% 0.58/0.80           = (k4_xboole_0 @ X21 @ X22))),
% 0.58/0.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.58/0.80  thf('119', plain,
% 0.58/0.80      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 0.58/0.80      inference('sup+', [status(thm)], ['117', '118'])).
% 0.58/0.80  thf('120', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.80  thf('121', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 0.58/0.80      inference('demod', [status(thm)], ['119', '120'])).
% 0.58/0.80  thf('122', plain, (((sk_A) = (sk_D))),
% 0.58/0.80      inference('demod', [status(thm)], ['73', '74', '98', '99', '100', '101'])).
% 0.58/0.80  thf('123', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['121', '122'])).
% 0.58/0.80  thf('124', plain, (((sk_B_1) = (sk_C_2))),
% 0.58/0.80      inference('sup+', [status(thm)], ['112', '123'])).
% 0.58/0.80  thf('125', plain, (((sk_C_2) != (sk_B_1))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('126', plain, ($false),
% 0.58/0.80      inference('simplify_reflect-', [status(thm)], ['124', '125'])).
% 0.58/0.80  
% 0.58/0.80  % SZS output end Refutation
% 0.58/0.80  
% 0.58/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
