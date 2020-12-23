%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zQl9Ucw6jH

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:59 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 362 expanded)
%              Number of leaves         :   28 ( 127 expanded)
%              Depth                    :   21
%              Number of atoms          :  900 (2795 expanded)
%              Number of equality atoms :   93 ( 292 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
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

thf('2',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_D ) @ sk_D )
    = ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('18',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','5'])).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
    = sk_B_1 ),
    inference(demod,[status(thm)],['16','17','18','23'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_D ),
    inference('sup-',[status(thm)],['27','32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['37','44','45'])).

thf('47',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('49',plain,(
    r1_tarski @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('51',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('53',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('55',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('57',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['46','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['24','58'])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('62',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_D ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('72',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('74',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('75',plain,(
    r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('77',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['75','76'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('78',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_xboole_0 @ X30 @ X31 )
      | ( r1_xboole_0 @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['72','79'])).

thf('81',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('88',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('89',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('90',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('91',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('92',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('95',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('97',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_xboole_0 @ X30 @ X31 )
      | ( r1_xboole_0 @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D ),
    inference('sup-',[status(thm)],['69','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('102',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('104',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('106',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = sk_C_1 ),
    inference(demod,[status(thm)],['62','106'])).

thf('108',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['46','57'])).

thf('109',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('110',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['59','110'])).

thf('112',plain,(
    sk_C_1 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['111','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zQl9Ucw6jH
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:45:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.58/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.76  % Solved by: fo/fo7.sh
% 0.58/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.76  % done 970 iterations in 0.310s
% 0.58/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.76  % SZS output start Refutation
% 0.58/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.76  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.76  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.76  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.76  thf(t72_xboole_1, conjecture,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.58/0.76         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.58/0.76       ( ( C ) = ( B ) ) ))).
% 0.58/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.76    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.58/0.76            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.58/0.76          ( ( C ) = ( B ) ) ) )),
% 0.58/0.76    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.58/0.76  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(t7_xboole_0, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.58/0.76          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.58/0.76  thf('1', plain,
% 0.58/0.76      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.58/0.76      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.76  thf(t4_xboole_0, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.76            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.76       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.58/0.76            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.58/0.76  thf('2', plain,
% 0.58/0.76      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.58/0.76          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.58/0.76      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.76  thf('3', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.76  thf('4', plain, (((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['0', '3'])).
% 0.58/0.76  thf(commutativity_k3_xboole_0, axiom,
% 0.58/0.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.58/0.76  thf('5', plain,
% 0.58/0.76      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.76  thf('6', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.58/0.76      inference('demod', [status(thm)], ['4', '5'])).
% 0.58/0.76  thf('7', plain,
% 0.58/0.76      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.76  thf(t47_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.58/0.76  thf('8', plain,
% 0.58/0.76      (![X20 : $i, X21 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 0.58/0.76           = (k4_xboole_0 @ X20 @ X21))),
% 0.58/0.76      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.58/0.76  thf('9', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.76           = (k4_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('sup+', [status(thm)], ['7', '8'])).
% 0.58/0.76  thf('10', plain,
% 0.58/0.76      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.58/0.76      inference('sup+', [status(thm)], ['6', '9'])).
% 0.58/0.76  thf(t3_boole, axiom,
% 0.58/0.76    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.76  thf('11', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.58/0.76      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.76  thf('12', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['10', '11'])).
% 0.58/0.76  thf(t39_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.76  thf('13', plain,
% 0.58/0.76      (![X12 : $i, X13 : $i]:
% 0.58/0.76         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.58/0.76           = (k2_xboole_0 @ X12 @ X13))),
% 0.58/0.76      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.58/0.76  thf(t40_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.58/0.76  thf('14', plain,
% 0.58/0.76      (![X15 : $i, X16 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.58/0.76           = (k4_xboole_0 @ X15 @ X16))),
% 0.58/0.76      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.76  thf('15', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.58/0.76           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.58/0.76  thf('16', plain,
% 0.58/0.76      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_D) @ sk_D)
% 0.58/0.76         = (k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_D @ sk_B_1)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['12', '15'])).
% 0.58/0.76  thf('17', plain,
% 0.58/0.76      (![X15 : $i, X16 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.58/0.76           = (k4_xboole_0 @ X15 @ X16))),
% 0.58/0.76      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.76  thf('18', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['10', '11'])).
% 0.58/0.76  thf('19', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.58/0.76      inference('demod', [status(thm)], ['4', '5'])).
% 0.58/0.76  thf('20', plain,
% 0.58/0.76      (![X20 : $i, X21 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 0.58/0.76           = (k4_xboole_0 @ X20 @ X21))),
% 0.58/0.76      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.58/0.76  thf('21', plain,
% 0.58/0.76      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 0.58/0.76      inference('sup+', [status(thm)], ['19', '20'])).
% 0.58/0.76  thf('22', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.58/0.76      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.76  thf('23', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 0.58/0.76      inference('demod', [status(thm)], ['21', '22'])).
% 0.58/0.76  thf('24', plain, (((k4_xboole_0 @ sk_B_1 @ sk_D) = (sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['16', '17', '18', '23'])).
% 0.58/0.76  thf(commutativity_k2_xboole_0, axiom,
% 0.58/0.76    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.58/0.76  thf('25', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.76  thf(t7_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.76  thf('26', plain,
% 0.58/0.76      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 0.58/0.76      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.58/0.76  thf('27', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['25', '26'])).
% 0.58/0.76  thf('28', plain,
% 0.58/0.76      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('29', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.76  thf('30', plain,
% 0.58/0.76      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.58/0.76      inference('demod', [status(thm)], ['28', '29'])).
% 0.58/0.76  thf(t43_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.58/0.76       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.58/0.76  thf('31', plain,
% 0.58/0.76      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.76         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.58/0.76          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.58/0.76  thf('32', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_A))
% 0.58/0.76          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D))),
% 0.58/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.58/0.76  thf('33', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_D)),
% 0.58/0.76      inference('sup-', [status(thm)], ['27', '32'])).
% 0.58/0.76  thf(t12_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.58/0.76  thf('34', plain,
% 0.58/0.76      (![X10 : $i, X11 : $i]:
% 0.58/0.76         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.58/0.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.76  thf('35', plain,
% 0.58/0.76      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_D) = (sk_D))),
% 0.58/0.76      inference('sup-', [status(thm)], ['33', '34'])).
% 0.58/0.76  thf('36', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.76  thf('37', plain,
% 0.58/0.76      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_A @ sk_C_1)) = (sk_D))),
% 0.58/0.76      inference('demod', [status(thm)], ['35', '36'])).
% 0.58/0.76  thf('38', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('39', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.76  thf('40', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.76  thf('41', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.76           = (k4_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('sup+', [status(thm)], ['7', '8'])).
% 0.58/0.76  thf('42', plain,
% 0.58/0.76      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.58/0.76      inference('sup+', [status(thm)], ['40', '41'])).
% 0.58/0.76  thf('43', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.58/0.76      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.76  thf('44', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['42', '43'])).
% 0.58/0.76  thf('45', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.76  thf('46', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_D))),
% 0.58/0.76      inference('demod', [status(thm)], ['37', '44', '45'])).
% 0.58/0.76  thf('47', plain,
% 0.58/0.76      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.58/0.76      inference('demod', [status(thm)], ['28', '29'])).
% 0.58/0.76  thf('48', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['25', '26'])).
% 0.58/0.76  thf('49', plain, ((r1_tarski @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.58/0.76      inference('sup+', [status(thm)], ['47', '48'])).
% 0.58/0.76  thf('50', plain,
% 0.58/0.76      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.76         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.58/0.76          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.58/0.76  thf('51', plain, ((r1_tarski @ (k4_xboole_0 @ sk_D @ sk_B_1) @ sk_A)),
% 0.58/0.76      inference('sup-', [status(thm)], ['49', '50'])).
% 0.58/0.76  thf('52', plain,
% 0.58/0.76      (![X10 : $i, X11 : $i]:
% 0.58/0.76         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.58/0.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.76  thf('53', plain,
% 0.58/0.76      (((k2_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B_1) @ sk_A) = (sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['51', '52'])).
% 0.58/0.76  thf('54', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.76  thf('55', plain,
% 0.58/0.76      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B_1)) = (sk_A))),
% 0.58/0.76      inference('demod', [status(thm)], ['53', '54'])).
% 0.58/0.76  thf('56', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['10', '11'])).
% 0.58/0.76  thf('57', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 0.58/0.76      inference('demod', [status(thm)], ['55', '56'])).
% 0.58/0.76  thf('58', plain, (((sk_D) = (sk_A))),
% 0.58/0.76      inference('sup+', [status(thm)], ['46', '57'])).
% 0.58/0.76  thf('59', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['24', '58'])).
% 0.58/0.76  thf('60', plain,
% 0.58/0.76      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.58/0.76      inference('demod', [status(thm)], ['28', '29'])).
% 0.58/0.76  thf('61', plain,
% 0.58/0.76      (![X15 : $i, X16 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.58/0.76           = (k4_xboole_0 @ X15 @ X16))),
% 0.58/0.76      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.76  thf('62', plain,
% 0.58/0.76      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D)
% 0.58/0.76         = (k4_xboole_0 @ sk_C_1 @ sk_D))),
% 0.58/0.76      inference('sup+', [status(thm)], ['60', '61'])).
% 0.58/0.76  thf('63', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('64', plain,
% 0.58/0.76      (![X5 : $i, X6 : $i]:
% 0.58/0.76         ((r1_xboole_0 @ X5 @ X6)
% 0.58/0.76          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.76  thf('65', plain,
% 0.58/0.76      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.76  thf('66', plain,
% 0.58/0.76      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.58/0.76          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.58/0.76      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.76  thf('67', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.76          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['65', '66'])).
% 0.58/0.76  thf('68', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['64', '67'])).
% 0.58/0.76  thf('69', plain, ((r1_xboole_0 @ sk_B_1 @ sk_D)),
% 0.58/0.76      inference('sup-', [status(thm)], ['63', '68'])).
% 0.58/0.76  thf('70', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('71', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['64', '67'])).
% 0.58/0.76  thf('72', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.58/0.76      inference('sup-', [status(thm)], ['70', '71'])).
% 0.58/0.76  thf('73', plain,
% 0.58/0.76      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.58/0.76      inference('demod', [status(thm)], ['28', '29'])).
% 0.58/0.76  thf('74', plain,
% 0.58/0.76      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 0.58/0.76      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.58/0.76  thf('75', plain, ((r1_tarski @ sk_C_1 @ (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.58/0.76      inference('sup+', [status(thm)], ['73', '74'])).
% 0.58/0.76  thf('76', plain,
% 0.58/0.76      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.76         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.58/0.76          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.58/0.76  thf('77', plain, ((r1_tarski @ (k4_xboole_0 @ sk_C_1 @ sk_B_1) @ sk_A)),
% 0.58/0.76      inference('sup-', [status(thm)], ['75', '76'])).
% 0.58/0.76  thf(t63_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.58/0.76       ( r1_xboole_0 @ A @ C ) ))).
% 0.58/0.76  thf('78', plain,
% 0.58/0.76      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.58/0.76         (~ (r1_tarski @ X29 @ X30)
% 0.58/0.76          | ~ (r1_xboole_0 @ X30 @ X31)
% 0.58/0.76          | (r1_xboole_0 @ X29 @ X31))),
% 0.58/0.76      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.58/0.76  thf('79', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((r1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_B_1) @ X0)
% 0.58/0.76          | ~ (r1_xboole_0 @ sk_A @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['77', '78'])).
% 0.58/0.76  thf('80', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_B_1) @ sk_C_1)),
% 0.58/0.76      inference('sup-', [status(thm)], ['72', '79'])).
% 0.58/0.76  thf('81', plain,
% 0.58/0.76      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.58/0.76      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.76  thf('82', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.76          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['65', '66'])).
% 0.58/0.76  thf('83', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['81', '82'])).
% 0.58/0.76  thf('84', plain,
% 0.58/0.76      (((k3_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_C_1 @ sk_B_1))
% 0.58/0.76         = (k1_xboole_0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['80', '83'])).
% 0.58/0.76  thf('85', plain,
% 0.58/0.76      (![X20 : $i, X21 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 0.58/0.76           = (k4_xboole_0 @ X20 @ X21))),
% 0.58/0.76      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.58/0.76  thf('86', plain,
% 0.58/0.76      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0)
% 0.58/0.76         = (k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_C_1 @ sk_B_1)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['84', '85'])).
% 0.58/0.76  thf('87', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.58/0.76      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.76  thf(t48_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.76  thf('88', plain,
% 0.58/0.76      (![X22 : $i, X23 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.58/0.76           = (k3_xboole_0 @ X22 @ X23))),
% 0.58/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.76  thf('89', plain,
% 0.58/0.76      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.76  thf('90', plain, (((sk_C_1) = (k3_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.58/0.76  thf(t51_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.58/0.76       ( A ) ))).
% 0.58/0.76  thf('91', plain,
% 0.58/0.76      (![X27 : $i, X28 : $i]:
% 0.58/0.76         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 0.58/0.76           = (X27))),
% 0.58/0.76      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.58/0.76  thf('92', plain,
% 0.58/0.76      (((k2_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (sk_B_1))),
% 0.58/0.76      inference('sup+', [status(thm)], ['90', '91'])).
% 0.58/0.76  thf('93', plain,
% 0.58/0.76      (![X12 : $i, X13 : $i]:
% 0.58/0.76         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.58/0.76           = (k2_xboole_0 @ X12 @ X13))),
% 0.58/0.76      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.58/0.76  thf('94', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.76  thf('95', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.58/0.76  thf('96', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['25', '26'])).
% 0.58/0.76  thf('97', plain,
% 0.58/0.76      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.58/0.76         (~ (r1_tarski @ X29 @ X30)
% 0.58/0.76          | ~ (r1_xboole_0 @ X30 @ X31)
% 0.58/0.76          | (r1_xboole_0 @ X29 @ X31))),
% 0.58/0.76      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.58/0.76  thf('98', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.76         ((r1_xboole_0 @ X0 @ X2)
% 0.58/0.76          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.58/0.76      inference('sup-', [status(thm)], ['96', '97'])).
% 0.58/0.76  thf('99', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (r1_xboole_0 @ sk_B_1 @ X0) | (r1_xboole_0 @ sk_C_1 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['95', '98'])).
% 0.58/0.76  thf('100', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D)),
% 0.58/0.76      inference('sup-', [status(thm)], ['69', '99'])).
% 0.58/0.76  thf('101', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.76  thf('102', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['100', '101'])).
% 0.58/0.76  thf('103', plain,
% 0.58/0.76      (![X20 : $i, X21 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 0.58/0.76           = (k4_xboole_0 @ X20 @ X21))),
% 0.58/0.76      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.58/0.76  thf('104', plain,
% 0.58/0.76      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_D))),
% 0.58/0.76      inference('sup+', [status(thm)], ['102', '103'])).
% 0.58/0.76  thf('105', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.58/0.76      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.76  thf('106', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_D))),
% 0.58/0.76      inference('demod', [status(thm)], ['104', '105'])).
% 0.58/0.76  thf('107', plain,
% 0.58/0.76      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D) = (sk_C_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['62', '106'])).
% 0.58/0.76  thf('108', plain, (((sk_D) = (sk_A))),
% 0.58/0.76      inference('sup+', [status(thm)], ['46', '57'])).
% 0.58/0.76  thf('109', plain,
% 0.58/0.76      (![X15 : $i, X16 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.58/0.76           = (k4_xboole_0 @ X15 @ X16))),
% 0.58/0.76      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.76  thf('110', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.58/0.76  thf('111', plain, (((sk_B_1) = (sk_C_1))),
% 0.58/0.76      inference('sup+', [status(thm)], ['59', '110'])).
% 0.58/0.76  thf('112', plain, (((sk_C_1) != (sk_B_1))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('113', plain, ($false),
% 0.58/0.76      inference('simplify_reflect-', [status(thm)], ['111', '112'])).
% 0.58/0.76  
% 0.58/0.76  % SZS output end Refutation
% 0.58/0.76  
% 0.58/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
