%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ESuos18PIT

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:53 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 261 expanded)
%              Number of leaves         :   21 ( 100 expanded)
%              Depth                    :   16
%              Number of atoms          :  671 (2111 expanded)
%              Number of equality atoms :   83 ( 261 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t71_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ B ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ C @ B ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
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
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','16','19'])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('33',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('46',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['24','25','26','27','38','39','40','41','42','43','44','45','46'])).

thf('48',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('55',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('58',plain,
    ( sk_C_1
    = ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['24','25','26','27','38','39','40','41','42','43','44','45','46'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('61',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('67',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('70',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['59','69'])).

thf('71',plain,(
    sk_A = sk_C_1 ),
    inference('sup+',[status(thm)],['58','70'])).

thf('72',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ESuos18PIT
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:34:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.39/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.63  % Solved by: fo/fo7.sh
% 0.39/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.63  % done 380 iterations in 0.156s
% 0.39/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.63  % SZS output start Refutation
% 0.39/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.63  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.63  thf(t71_xboole_1, conjecture,
% 0.39/0.63    (![A:$i,B:$i,C:$i]:
% 0.39/0.63     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.39/0.63         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.39/0.63       ( ( A ) = ( C ) ) ))).
% 0.39/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.63        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.39/0.63            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.39/0.63          ( ( A ) = ( C ) ) ) )),
% 0.39/0.63    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.39/0.63  thf('0', plain,
% 0.39/0.63      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf(t40_xboole_1, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.63  thf('1', plain,
% 0.39/0.63      (![X14 : $i, X15 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.39/0.63           = (k4_xboole_0 @ X14 @ X15))),
% 0.39/0.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.63  thf('2', plain,
% 0.39/0.63      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.39/0.63         = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.39/0.63      inference('sup+', [status(thm)], ['0', '1'])).
% 0.39/0.63  thf('3', plain,
% 0.39/0.63      (![X14 : $i, X15 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.39/0.63           = (k4_xboole_0 @ X14 @ X15))),
% 0.39/0.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.63  thf('4', plain,
% 0.39/0.63      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.39/0.63      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.63  thf(t48_xboole_1, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.63  thf('5', plain,
% 0.39/0.63      (![X19 : $i, X20 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.39/0.63           = (k3_xboole_0 @ X19 @ X20))),
% 0.39/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.63  thf('6', plain,
% 0.39/0.63      (((k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 0.39/0.63         = (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.39/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.39/0.63  thf(t39_xboole_1, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.63  thf('7', plain,
% 0.39/0.63      (![X11 : $i, X12 : $i]:
% 0.39/0.63         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.39/0.63           = (k2_xboole_0 @ X11 @ X12))),
% 0.39/0.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.63  thf('8', plain,
% 0.39/0.63      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ 
% 0.39/0.63         (k3_xboole_0 @ sk_C_1 @ sk_B_1))
% 0.39/0.63         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.39/0.63      inference('sup+', [status(thm)], ['6', '7'])).
% 0.39/0.63  thf(commutativity_k2_xboole_0, axiom,
% 0.39/0.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.39/0.63  thf('9', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.63  thf('10', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.63  thf('11', plain,
% 0.39/0.63      (((k2_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_B_1) @ 
% 0.39/0.63         (k4_xboole_0 @ sk_A @ sk_B_1))
% 0.39/0.63         = (k2_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B_1)))),
% 0.39/0.63      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.39/0.63  thf('12', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf(t7_xboole_0, axiom,
% 0.39/0.63    (![A:$i]:
% 0.39/0.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.39/0.63          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.39/0.63  thf('13', plain,
% 0.39/0.63      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.39/0.63      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.63  thf(t4_xboole_0, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.63            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.63       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.63            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.39/0.63  thf('14', plain,
% 0.39/0.63      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.39/0.63          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.39/0.63      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.39/0.63  thf('15', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.63  thf('16', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['12', '15'])).
% 0.39/0.63  thf('17', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.63  thf(t1_boole, axiom,
% 0.39/0.63    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.63  thf('18', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.63  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.63      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.63  thf('20', plain,
% 0.39/0.63      (((k4_xboole_0 @ sk_A @ sk_B_1)
% 0.39/0.63         = (k2_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B_1)))),
% 0.39/0.63      inference('demod', [status(thm)], ['11', '16', '19'])).
% 0.39/0.63  thf('21', plain,
% 0.39/0.63      (![X11 : $i, X12 : $i]:
% 0.39/0.63         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.39/0.63           = (k2_xboole_0 @ X11 @ X12))),
% 0.39/0.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.63  thf('22', plain,
% 0.39/0.63      (![X14 : $i, X15 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.39/0.63           = (k4_xboole_0 @ X14 @ X15))),
% 0.39/0.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.63  thf('23', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.39/0.63           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.39/0.63      inference('sup+', [status(thm)], ['21', '22'])).
% 0.39/0.63  thf('24', plain,
% 0.39/0.63      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ 
% 0.39/0.63         (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ sk_C_1))
% 0.39/0.63         = (k4_xboole_0 @ sk_C_1 @ 
% 0.39/0.63            (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ sk_C_1)))),
% 0.39/0.63      inference('sup+', [status(thm)], ['20', '23'])).
% 0.39/0.63  thf(t41_xboole_1, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i]:
% 0.39/0.63     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.63       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.63  thf('25', plain,
% 0.39/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.39/0.63           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.63  thf('26', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.63  thf('27', plain,
% 0.39/0.63      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('28', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.63  thf('29', plain,
% 0.39/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.39/0.63           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.63  thf(t3_boole, axiom,
% 0.39/0.63    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.63  thf('30', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.39/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.63  thf('31', plain,
% 0.39/0.63      (![X19 : $i, X20 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.39/0.63           = (k3_xboole_0 @ X19 @ X20))),
% 0.39/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.63  thf('32', plain,
% 0.39/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.63      inference('sup+', [status(thm)], ['30', '31'])).
% 0.39/0.63  thf(t2_boole, axiom,
% 0.39/0.63    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.63  thf('33', plain,
% 0.39/0.63      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.63      inference('cnf', [status(esa)], [t2_boole])).
% 0.39/0.63  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.63      inference('demod', [status(thm)], ['32', '33'])).
% 0.39/0.63  thf('35', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.39/0.63           = (k1_xboole_0))),
% 0.39/0.63      inference('sup+', [status(thm)], ['29', '34'])).
% 0.39/0.63  thf('36', plain,
% 0.39/0.63      (![X11 : $i, X12 : $i]:
% 0.39/0.63         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.39/0.63           = (k2_xboole_0 @ X11 @ X12))),
% 0.39/0.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.63  thf('37', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.39/0.63      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.63  thf('38', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.39/0.63      inference('sup+', [status(thm)], ['28', '37'])).
% 0.39/0.63  thf('39', plain,
% 0.39/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.39/0.63           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.63  thf('40', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.63  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.63      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.63  thf('42', plain,
% 0.39/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.39/0.63           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.63  thf('43', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.63  thf('44', plain,
% 0.39/0.63      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('45', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.39/0.63      inference('sup+', [status(thm)], ['28', '37'])).
% 0.39/0.63  thf('46', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.39/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.63  thf('47', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_C_1))),
% 0.39/0.63      inference('demod', [status(thm)],
% 0.39/0.63                ['24', '25', '26', '27', '38', '39', '40', '41', '42', '43', 
% 0.39/0.63                 '44', '45', '46'])).
% 0.39/0.63  thf('48', plain,
% 0.39/0.63      (![X19 : $i, X20 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.39/0.63           = (k3_xboole_0 @ X19 @ X20))),
% 0.39/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.63  thf('49', plain,
% 0.39/0.63      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.39/0.63      inference('sup+', [status(thm)], ['47', '48'])).
% 0.39/0.63  thf('50', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('51', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.63  thf('52', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.39/0.63  thf('53', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.39/0.63      inference('sup+', [status(thm)], ['49', '52'])).
% 0.39/0.63  thf('54', plain,
% 0.39/0.63      (![X11 : $i, X12 : $i]:
% 0.39/0.63         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.39/0.63           = (k2_xboole_0 @ X11 @ X12))),
% 0.39/0.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.63  thf('55', plain,
% 0.39/0.63      (((k2_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 0.39/0.63      inference('sup+', [status(thm)], ['53', '54'])).
% 0.39/0.63  thf('56', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.63  thf('57', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.63  thf('58', plain, (((sk_C_1) = (k2_xboole_0 @ sk_A @ sk_C_1))),
% 0.39/0.63      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.39/0.63  thf('59', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_C_1))),
% 0.39/0.63      inference('demod', [status(thm)],
% 0.39/0.63                ['24', '25', '26', '27', '38', '39', '40', '41', '42', '43', 
% 0.39/0.63                 '44', '45', '46'])).
% 0.39/0.63  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.63      inference('demod', [status(thm)], ['32', '33'])).
% 0.39/0.63  thf('61', plain,
% 0.39/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.39/0.63           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.63  thf('62', plain,
% 0.39/0.63      (![X11 : $i, X12 : $i]:
% 0.39/0.63         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.39/0.63           = (k2_xboole_0 @ X11 @ X12))),
% 0.39/0.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.63  thf('63', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.63         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.39/0.63           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.39/0.63      inference('sup+', [status(thm)], ['61', '62'])).
% 0.39/0.63  thf('64', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.39/0.63           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 0.39/0.63      inference('sup+', [status(thm)], ['60', '63'])).
% 0.39/0.63  thf('65', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.63  thf('66', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.63  thf('67', plain,
% 0.39/0.63      (![X14 : $i, X15 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.39/0.63           = (k4_xboole_0 @ X14 @ X15))),
% 0.39/0.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.63  thf('68', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.39/0.63           = (k4_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('sup+', [status(thm)], ['66', '67'])).
% 0.39/0.63  thf('69', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.63      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.39/0.63  thf('70', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_C_1))),
% 0.39/0.63      inference('sup+', [status(thm)], ['59', '69'])).
% 0.39/0.63  thf('71', plain, (((sk_A) = (sk_C_1))),
% 0.39/0.63      inference('sup+', [status(thm)], ['58', '70'])).
% 0.39/0.63  thf('72', plain, (((sk_A) != (sk_C_1))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('73', plain, ($false),
% 0.39/0.63      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.39/0.63  
% 0.39/0.63  % SZS output end Refutation
% 0.39/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
