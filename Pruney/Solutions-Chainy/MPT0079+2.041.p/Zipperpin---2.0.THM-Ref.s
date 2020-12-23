%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WTeTxKRTSC

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:02 EST 2020

% Result     : Theorem 6.48s
% Output     : Refutation 6.48s
% Verified   : 
% Statistics : Number of formulae       :  216 (11054 expanded)
%              Number of leaves         :   21 (3784 expanded)
%              Depth                    :   37
%              Number of atoms          : 1632 (85475 expanded)
%              Number of equality atoms :  206 (11467 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
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
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ X0 )
      = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','18'])).

thf('20',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ X0 @ sk_A ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('26',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ X0 @ sk_A ) )
      = ( k4_xboole_0 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['19','30'])).

thf('32',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['4','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['4','33'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_C )
    = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_C )
    = ( k4_xboole_0 @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C )
    = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('54',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('56',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('57',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','58'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('60',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k2_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','61'])).

thf('63',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_C )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('65',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('66',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','61'])).

thf('68',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k2_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('70',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k2_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','61'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('74',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_D ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70','71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','61'])).

thf('76',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_D ) @ sk_B )
    = ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_D ) @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k2_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('79',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k2_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('80',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','61'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('83',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','78','79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('85',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_A )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('87',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_D ) @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ X0 @ sk_A ) )
      = ( k4_xboole_0 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('89',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_D ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ X0 @ sk_A ) )
      = ( k4_xboole_0 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('91',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','78','79','80','81','82'])).

thf('92',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('93',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('94',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('96',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_D ) )
    = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['91','98'])).

thf('100',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('102',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('104',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['99','104'])).

thf('106',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['89','90','105'])).

thf('107',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('108',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_D @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('114',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( sk_D
    = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['43','114'])).

thf('116',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('117',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['4','33'])).

thf('121',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['4','33'])).

thf('122',plain,
    ( sk_C
    = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('124',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_C )
    = ( k4_xboole_0 @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('128',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('129',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('131',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['132','135'])).

thf('137',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['129','136'])).

thf('138',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['132','135'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['138','143'])).

thf('145',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['137','144'])).

thf('146',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('147',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('149',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('152',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['126','149','150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('154',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_C )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['127','128'])).

thf('156',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('157',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('159',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['127','128'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('162',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['160','165'])).

thf('167',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('169',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('171',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('173',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['170','173'])).

thf('175',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['169','176'])).

thf('178',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['166','177'])).

thf('179',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['159','178'])).

thf('180',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('181',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('183',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('185',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('187',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['34','185','186'])).

thf('188',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['138','143'])).

thf('189',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['183','184'])).

thf('190',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    sk_C = sk_B ),
    inference('sup+',[status(thm)],['187','190'])).

thf('192',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['191','192'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WTeTxKRTSC
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.48/6.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.48/6.73  % Solved by: fo/fo7.sh
% 6.48/6.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.48/6.73  % done 2993 iterations in 6.246s
% 6.48/6.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.48/6.73  % SZS output start Refutation
% 6.48/6.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.48/6.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.48/6.73  thf(sk_A_type, type, sk_A: $i).
% 6.48/6.73  thf(sk_C_type, type, sk_C: $i).
% 6.48/6.73  thf(sk_D_type, type, sk_D: $i).
% 6.48/6.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.48/6.73  thf(sk_B_type, type, sk_B: $i).
% 6.48/6.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.48/6.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.48/6.73  thf(t72_xboole_1, conjecture,
% 6.48/6.73    (![A:$i,B:$i,C:$i,D:$i]:
% 6.48/6.73     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 6.48/6.73         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 6.48/6.73       ( ( C ) = ( B ) ) ))).
% 6.48/6.73  thf(zf_stmt_0, negated_conjecture,
% 6.48/6.73    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 6.48/6.73        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 6.48/6.73            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 6.48/6.73          ( ( C ) = ( B ) ) ) )),
% 6.48/6.73    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 6.48/6.73  thf('0', plain,
% 6.48/6.73      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 6.48/6.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.48/6.73  thf(commutativity_k2_xboole_0, axiom,
% 6.48/6.73    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 6.48/6.73  thf('1', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.48/6.73  thf('2', plain,
% 6.48/6.73      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 6.48/6.73      inference('demod', [status(thm)], ['0', '1'])).
% 6.48/6.73  thf(t40_xboole_1, axiom,
% 6.48/6.73    (![A:$i,B:$i]:
% 6.48/6.73     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 6.48/6.73  thf('3', plain,
% 6.48/6.73      (![X6 : $i, X7 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 6.48/6.73           = (k4_xboole_0 @ X6 @ X7))),
% 6.48/6.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 6.48/6.73  thf('4', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 6.48/6.73         = (k4_xboole_0 @ sk_C @ sk_D))),
% 6.48/6.73      inference('sup+', [status(thm)], ['2', '3'])).
% 6.48/6.73  thf('5', plain,
% 6.48/6.73      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 6.48/6.73      inference('demod', [status(thm)], ['0', '1'])).
% 6.48/6.73  thf('6', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.48/6.73  thf(t46_xboole_1, axiom,
% 6.48/6.73    (![A:$i,B:$i]:
% 6.48/6.73     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 6.48/6.73  thf('7', plain,
% 6.48/6.73      (![X11 : $i, X12 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 6.48/6.73      inference('cnf', [status(esa)], [t46_xboole_1])).
% 6.48/6.73  thf('8', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['6', '7'])).
% 6.48/6.73  thf('9', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['5', '8'])).
% 6.48/6.73  thf('10', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 6.48/6.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.48/6.73  thf(d7_xboole_0, axiom,
% 6.48/6.73    (![A:$i,B:$i]:
% 6.48/6.73     ( ( r1_xboole_0 @ A @ B ) <=>
% 6.48/6.73       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 6.48/6.73  thf('11', plain,
% 6.48/6.73      (![X2 : $i, X3 : $i]:
% 6.48/6.73         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 6.48/6.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.48/6.73  thf('12', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 6.48/6.73      inference('sup-', [status(thm)], ['10', '11'])).
% 6.48/6.73  thf(t47_xboole_1, axiom,
% 6.48/6.73    (![A:$i,B:$i]:
% 6.48/6.73     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 6.48/6.73  thf('13', plain,
% 6.48/6.73      (![X13 : $i, X14 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 6.48/6.73           = (k4_xboole_0 @ X13 @ X14))),
% 6.48/6.73      inference('cnf', [status(esa)], [t47_xboole_1])).
% 6.48/6.73  thf('14', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B))),
% 6.48/6.73      inference('sup+', [status(thm)], ['12', '13'])).
% 6.48/6.73  thf(t3_boole, axiom,
% 6.48/6.73    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 6.48/6.73  thf('15', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 6.48/6.73      inference('cnf', [status(esa)], [t3_boole])).
% 6.48/6.73  thf('16', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 6.48/6.73      inference('demod', [status(thm)], ['14', '15'])).
% 6.48/6.73  thf(t41_xboole_1, axiom,
% 6.48/6.73    (![A:$i,B:$i,C:$i]:
% 6.48/6.73     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 6.48/6.73       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 6.48/6.73  thf('17', plain,
% 6.48/6.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 6.48/6.73           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t41_xboole_1])).
% 6.48/6.73  thf('18', plain,
% 6.48/6.73      (![X0 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ sk_D @ X0)
% 6.48/6.73           = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ X0)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['16', '17'])).
% 6.48/6.73  thf('19', plain, (((k4_xboole_0 @ sk_D @ sk_A) = (k1_xboole_0))),
% 6.48/6.73      inference('demod', [status(thm)], ['9', '18'])).
% 6.48/6.73  thf('20', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 6.48/6.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.48/6.73  thf('21', plain,
% 6.48/6.73      (![X2 : $i, X3 : $i]:
% 6.48/6.73         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 6.48/6.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.48/6.73  thf('22', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 6.48/6.73      inference('sup-', [status(thm)], ['20', '21'])).
% 6.48/6.73  thf(t52_xboole_1, axiom,
% 6.48/6.73    (![A:$i,B:$i,C:$i]:
% 6.48/6.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 6.48/6.73       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 6.48/6.73  thf('23', plain,
% 6.48/6.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 6.48/6.73           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 6.48/6.73              (k3_xboole_0 @ X21 @ X23)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t52_xboole_1])).
% 6.48/6.73  thf('24', plain,
% 6.48/6.73      (![X0 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ X0 @ sk_A))
% 6.48/6.73           = (k2_xboole_0 @ (k4_xboole_0 @ sk_C @ X0) @ k1_xboole_0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['22', '23'])).
% 6.48/6.73  thf('25', plain,
% 6.48/6.73      (![X6 : $i, X7 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 6.48/6.73           = (k4_xboole_0 @ X6 @ X7))),
% 6.48/6.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 6.48/6.73  thf('26', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 6.48/6.73      inference('cnf', [status(esa)], [t3_boole])).
% 6.48/6.73  thf('27', plain,
% 6.48/6.73      (![X0 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['25', '26'])).
% 6.48/6.73  thf('28', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 6.48/6.73      inference('cnf', [status(esa)], [t3_boole])).
% 6.48/6.73  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['27', '28'])).
% 6.48/6.73  thf('30', plain,
% 6.48/6.73      (![X0 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ X0 @ sk_A))
% 6.48/6.73           = (k4_xboole_0 @ sk_C @ X0))),
% 6.48/6.73      inference('demod', [status(thm)], ['24', '29'])).
% 6.48/6.73  thf('31', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_D))),
% 6.48/6.73      inference('sup+', [status(thm)], ['19', '30'])).
% 6.48/6.73  thf('32', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 6.48/6.73      inference('cnf', [status(esa)], [t3_boole])).
% 6.48/6.73  thf('33', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_D))),
% 6.48/6.73      inference('demod', [status(thm)], ['31', '32'])).
% 6.48/6.73  thf('34', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D) = (sk_C))),
% 6.48/6.73      inference('demod', [status(thm)], ['4', '33'])).
% 6.48/6.73  thf('35', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D) = (sk_C))),
% 6.48/6.73      inference('demod', [status(thm)], ['4', '33'])).
% 6.48/6.73  thf(t48_xboole_1, axiom,
% 6.48/6.73    (![A:$i,B:$i]:
% 6.48/6.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 6.48/6.73  thf('36', plain,
% 6.48/6.73      (![X15 : $i, X16 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 6.48/6.73           = (k3_xboole_0 @ X15 @ X16))),
% 6.48/6.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.48/6.73  thf('37', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_C)
% 6.48/6.73         = (k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D))),
% 6.48/6.73      inference('sup+', [status(thm)], ['35', '36'])).
% 6.48/6.73  thf('38', plain,
% 6.48/6.73      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 6.48/6.73      inference('demod', [status(thm)], ['0', '1'])).
% 6.48/6.73  thf('39', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.48/6.73  thf('40', plain,
% 6.48/6.73      (![X6 : $i, X7 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 6.48/6.73           = (k4_xboole_0 @ X6 @ X7))),
% 6.48/6.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 6.48/6.73  thf('41', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 6.48/6.73           = (k4_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('sup+', [status(thm)], ['39', '40'])).
% 6.48/6.73  thf('42', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_C)
% 6.48/6.73         = (k4_xboole_0 @ sk_D @ sk_C))),
% 6.48/6.73      inference('sup+', [status(thm)], ['38', '41'])).
% 6.48/6.73  thf('43', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_D @ sk_C)
% 6.48/6.73         = (k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D))),
% 6.48/6.73      inference('demod', [status(thm)], ['37', '42'])).
% 6.48/6.73  thf('44', plain,
% 6.48/6.73      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 6.48/6.73      inference('demod', [status(thm)], ['0', '1'])).
% 6.48/6.73  thf('45', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.48/6.73  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['27', '28'])).
% 6.48/6.73  thf('47', plain,
% 6.48/6.73      (![X11 : $i, X12 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 6.48/6.73      inference('cnf', [status(esa)], [t46_xboole_1])).
% 6.48/6.73  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['46', '47'])).
% 6.48/6.73  thf('49', plain,
% 6.48/6.73      (![X15 : $i, X16 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 6.48/6.73           = (k3_xboole_0 @ X15 @ X16))),
% 6.48/6.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.48/6.73  thf('50', plain,
% 6.48/6.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['48', '49'])).
% 6.48/6.73  thf('51', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 6.48/6.73      inference('cnf', [status(esa)], [t3_boole])).
% 6.48/6.73  thf('52', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 6.48/6.73      inference('demod', [status(thm)], ['50', '51'])).
% 6.48/6.73  thf('53', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 6.48/6.73      inference('cnf', [status(esa)], [t3_boole])).
% 6.48/6.73  thf('54', plain,
% 6.48/6.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 6.48/6.73           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 6.48/6.73              (k3_xboole_0 @ X21 @ X23)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t52_xboole_1])).
% 6.48/6.73  thf('55', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 6.48/6.73           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['53', '54'])).
% 6.48/6.73  thf(t4_boole, axiom,
% 6.48/6.73    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 6.48/6.73  thf('56', plain,
% 6.48/6.73      (![X17 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 6.48/6.73      inference('cnf', [status(esa)], [t4_boole])).
% 6.48/6.73  thf('57', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 6.48/6.73      inference('cnf', [status(esa)], [t3_boole])).
% 6.48/6.73  thf('58', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.48/6.73      inference('demod', [status(thm)], ['55', '56', '57'])).
% 6.48/6.73  thf('59', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['52', '58'])).
% 6.48/6.73  thf(t4_xboole_1, axiom,
% 6.48/6.73    (![A:$i,B:$i,C:$i]:
% 6.48/6.73     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 6.48/6.73       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 6.48/6.73  thf('60', plain,
% 6.48/6.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.48/6.73         ((k2_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X20)
% 6.48/6.73           = (k2_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t4_xboole_1])).
% 6.48/6.73  thf('61', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k2_xboole_0 @ X0 @ X1)
% 6.48/6.73           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['59', '60'])).
% 6.48/6.73  thf('62', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k2_xboole_0 @ X0 @ X1)
% 6.48/6.73           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['45', '61'])).
% 6.48/6.73  thf('63', plain,
% 6.48/6.73      (((k2_xboole_0 @ sk_D @ sk_C)
% 6.48/6.73         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['44', '62'])).
% 6.48/6.73  thf('64', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.48/6.73  thf('65', plain,
% 6.48/6.73      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 6.48/6.73      inference('demod', [status(thm)], ['0', '1'])).
% 6.48/6.73  thf('66', plain,
% 6.48/6.73      (((k2_xboole_0 @ sk_B @ sk_A)
% 6.48/6.73         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 6.48/6.73      inference('demod', [status(thm)], ['63', '64', '65'])).
% 6.48/6.73  thf('67', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k2_xboole_0 @ X0 @ X1)
% 6.48/6.73           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['45', '61'])).
% 6.48/6.73  thf('68', plain,
% 6.48/6.73      (((k2_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 6.48/6.73         = (k2_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 6.48/6.73            (k2_xboole_0 @ sk_B @ sk_A)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['66', '67'])).
% 6.48/6.73  thf('69', plain,
% 6.48/6.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.48/6.73         ((k2_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X20)
% 6.48/6.73           = (k2_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t4_xboole_1])).
% 6.48/6.73  thf('70', plain,
% 6.48/6.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.48/6.73         ((k2_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X20)
% 6.48/6.73           = (k2_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t4_xboole_1])).
% 6.48/6.73  thf('71', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k2_xboole_0 @ X0 @ X1)
% 6.48/6.73           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['45', '61'])).
% 6.48/6.73  thf('72', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.48/6.73  thf('73', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k2_xboole_0 @ X0 @ X1)
% 6.48/6.73           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['59', '60'])).
% 6.48/6.73  thf('74', plain,
% 6.48/6.73      (((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_D))
% 6.48/6.73         = (k2_xboole_0 @ sk_B @ sk_A))),
% 6.48/6.73      inference('demod', [status(thm)], ['68', '69', '70', '71', '72', '73'])).
% 6.48/6.73  thf('75', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k2_xboole_0 @ X0 @ X1)
% 6.48/6.73           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['45', '61'])).
% 6.48/6.73  thf('76', plain,
% 6.48/6.73      (((k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_D) @ sk_B)
% 6.48/6.73         = (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_D) @ 
% 6.48/6.73            (k2_xboole_0 @ sk_B @ sk_A)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['74', '75'])).
% 6.48/6.73  thf('77', plain,
% 6.48/6.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.48/6.73         ((k2_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X20)
% 6.48/6.73           = (k2_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t4_xboole_1])).
% 6.48/6.73  thf('78', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.48/6.73  thf('79', plain,
% 6.48/6.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.48/6.73         ((k2_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X20)
% 6.48/6.73           = (k2_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t4_xboole_1])).
% 6.48/6.73  thf('80', plain,
% 6.48/6.73      (((k2_xboole_0 @ sk_B @ sk_A)
% 6.48/6.73         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 6.48/6.73      inference('demod', [status(thm)], ['63', '64', '65'])).
% 6.48/6.73  thf('81', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k2_xboole_0 @ X0 @ X1)
% 6.48/6.73           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['45', '61'])).
% 6.48/6.73  thf('82', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.48/6.73  thf('83', plain,
% 6.48/6.73      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_D))
% 6.48/6.73         = (k2_xboole_0 @ sk_B @ sk_A))),
% 6.48/6.73      inference('demod', [status(thm)],
% 6.48/6.73                ['76', '77', '78', '79', '80', '81', '82'])).
% 6.48/6.73  thf('84', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 6.48/6.73           = (k4_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('sup+', [status(thm)], ['39', '40'])).
% 6.48/6.73  thf('85', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_A)
% 6.48/6.73         = (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_D) @ sk_A))),
% 6.48/6.73      inference('sup+', [status(thm)], ['83', '84'])).
% 6.48/6.73  thf('86', plain,
% 6.48/6.73      (![X6 : $i, X7 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 6.48/6.73           = (k4_xboole_0 @ X6 @ X7))),
% 6.48/6.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 6.48/6.73  thf('87', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_B @ sk_A)
% 6.48/6.73         = (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_D) @ sk_A))),
% 6.48/6.73      inference('demod', [status(thm)], ['85', '86'])).
% 6.48/6.73  thf('88', plain,
% 6.48/6.73      (![X0 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ X0 @ sk_A))
% 6.48/6.73           = (k4_xboole_0 @ sk_C @ X0))),
% 6.48/6.73      inference('demod', [status(thm)], ['24', '29'])).
% 6.48/6.73  thf('89', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_A))
% 6.48/6.73         = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_D)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['87', '88'])).
% 6.48/6.73  thf('90', plain,
% 6.48/6.73      (![X0 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ X0 @ sk_A))
% 6.48/6.73           = (k4_xboole_0 @ sk_C @ X0))),
% 6.48/6.73      inference('demod', [status(thm)], ['24', '29'])).
% 6.48/6.73  thf('91', plain,
% 6.48/6.73      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_D))
% 6.48/6.73         = (k2_xboole_0 @ sk_B @ sk_A))),
% 6.48/6.73      inference('demod', [status(thm)],
% 6.48/6.73                ['76', '77', '78', '79', '80', '81', '82'])).
% 6.48/6.73  thf('92', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 6.48/6.73      inference('sup-', [status(thm)], ['20', '21'])).
% 6.48/6.73  thf('93', plain,
% 6.48/6.73      (![X13 : $i, X14 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 6.48/6.73           = (k4_xboole_0 @ X13 @ X14))),
% 6.48/6.73      inference('cnf', [status(esa)], [t47_xboole_1])).
% 6.48/6.73  thf('94', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 6.48/6.73      inference('sup+', [status(thm)], ['92', '93'])).
% 6.48/6.73  thf('95', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 6.48/6.73      inference('cnf', [status(esa)], [t3_boole])).
% 6.48/6.73  thf('96', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 6.48/6.73      inference('demod', [status(thm)], ['94', '95'])).
% 6.48/6.73  thf('97', plain,
% 6.48/6.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 6.48/6.73           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t41_xboole_1])).
% 6.48/6.73  thf('98', plain,
% 6.48/6.73      (![X0 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ sk_C @ X0)
% 6.48/6.73           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['96', '97'])).
% 6.48/6.73  thf('99', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_D))
% 6.48/6.73         = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['91', '98'])).
% 6.48/6.73  thf('100', plain,
% 6.48/6.73      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 6.48/6.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.48/6.73  thf('101', plain,
% 6.48/6.73      (![X11 : $i, X12 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 6.48/6.73      inference('cnf', [status(esa)], [t46_xboole_1])).
% 6.48/6.73  thf('102', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['100', '101'])).
% 6.48/6.73  thf('103', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.48/6.73  thf('104', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 6.48/6.73      inference('demod', [status(thm)], ['102', '103'])).
% 6.48/6.73  thf('105', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_D)) = (k1_xboole_0))),
% 6.48/6.73      inference('demod', [status(thm)], ['99', '104'])).
% 6.48/6.73  thf('106', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 6.48/6.73      inference('demod', [status(thm)], ['89', '90', '105'])).
% 6.48/6.73  thf('107', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 6.48/6.73      inference('sup-', [status(thm)], ['10', '11'])).
% 6.48/6.73  thf('108', plain,
% 6.48/6.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 6.48/6.73           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 6.48/6.73              (k3_xboole_0 @ X21 @ X23)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t52_xboole_1])).
% 6.48/6.73  thf('109', plain,
% 6.48/6.73      (![X0 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ sk_D @ (k4_xboole_0 @ X0 @ sk_B))
% 6.48/6.73           = (k2_xboole_0 @ (k4_xboole_0 @ sk_D @ X0) @ k1_xboole_0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['107', '108'])).
% 6.48/6.73  thf('110', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['27', '28'])).
% 6.48/6.73  thf('111', plain,
% 6.48/6.73      (![X0 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ sk_D @ (k4_xboole_0 @ X0 @ sk_B))
% 6.48/6.73           = (k4_xboole_0 @ sk_D @ X0))),
% 6.48/6.73      inference('demod', [status(thm)], ['109', '110'])).
% 6.48/6.73  thf('112', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_C))),
% 6.48/6.73      inference('sup+', [status(thm)], ['106', '111'])).
% 6.48/6.73  thf('113', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 6.48/6.73      inference('cnf', [status(esa)], [t3_boole])).
% 6.48/6.73  thf('114', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_C))),
% 6.48/6.73      inference('demod', [status(thm)], ['112', '113'])).
% 6.48/6.73  thf('115', plain,
% 6.48/6.73      (((sk_D) = (k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D))),
% 6.48/6.73      inference('demod', [status(thm)], ['43', '114'])).
% 6.48/6.73  thf('116', plain,
% 6.48/6.73      (![X15 : $i, X16 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 6.48/6.73           = (k3_xboole_0 @ X15 @ X16))),
% 6.48/6.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.48/6.73  thf('117', plain,
% 6.48/6.73      (![X15 : $i, X16 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 6.48/6.73           = (k3_xboole_0 @ X15 @ X16))),
% 6.48/6.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.48/6.73  thf('118', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 6.48/6.73           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['116', '117'])).
% 6.48/6.73  thf('119', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 6.48/6.73         = (k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 6.48/6.73            (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['115', '118'])).
% 6.48/6.73  thf('120', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D) = (sk_C))),
% 6.48/6.73      inference('demod', [status(thm)], ['4', '33'])).
% 6.48/6.73  thf('121', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D) = (sk_C))),
% 6.48/6.73      inference('demod', [status(thm)], ['4', '33'])).
% 6.48/6.73  thf('122', plain,
% 6.48/6.73      (((sk_C) = (k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 6.48/6.73      inference('demod', [status(thm)], ['119', '120', '121'])).
% 6.48/6.73  thf('123', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 6.48/6.73           = (k4_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('sup+', [status(thm)], ['39', '40'])).
% 6.48/6.73  thf('124', plain,
% 6.48/6.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 6.48/6.73           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 6.48/6.73              (k3_xboole_0 @ X21 @ X23)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t52_xboole_1])).
% 6.48/6.73  thf('125', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2))
% 6.48/6.73           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 6.48/6.73              (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['123', '124'])).
% 6.48/6.73  thf('126', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 6.48/6.73         (k4_xboole_0 @ sk_B @ sk_C))
% 6.48/6.73         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 6.48/6.73      inference('sup+', [status(thm)], ['122', '125'])).
% 6.48/6.73  thf('127', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_C)
% 6.48/6.73         = (k4_xboole_0 @ sk_D @ sk_C))),
% 6.48/6.73      inference('sup+', [status(thm)], ['38', '41'])).
% 6.48/6.73  thf('128', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_C))),
% 6.48/6.73      inference('demod', [status(thm)], ['112', '113'])).
% 6.48/6.73  thf('129', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_C) = (sk_D))),
% 6.48/6.73      inference('demod', [status(thm)], ['127', '128'])).
% 6.48/6.73  thf('130', plain,
% 6.48/6.73      (![X11 : $i, X12 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 6.48/6.73      inference('cnf', [status(esa)], [t46_xboole_1])).
% 6.48/6.73  thf('131', plain,
% 6.48/6.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 6.48/6.73           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 6.48/6.73              (k3_xboole_0 @ X21 @ X23)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t52_xboole_1])).
% 6.48/6.73  thf('132', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X0))
% 6.48/6.73           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['130', '131'])).
% 6.48/6.73  thf('133', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['27', '28'])).
% 6.48/6.73  thf('134', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.48/6.73  thf('135', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['133', '134'])).
% 6.48/6.73  thf('136', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X0))
% 6.48/6.73           = (k3_xboole_0 @ X1 @ X0))),
% 6.48/6.73      inference('demod', [status(thm)], ['132', '135'])).
% 6.48/6.73  thf('137', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_B @ sk_D) = (k3_xboole_0 @ sk_B @ sk_C))),
% 6.48/6.73      inference('sup+', [status(thm)], ['129', '136'])).
% 6.48/6.73  thf('138', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 6.48/6.73      inference('demod', [status(thm)], ['14', '15'])).
% 6.48/6.73  thf('139', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 6.48/6.73           = (k4_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('sup+', [status(thm)], ['39', '40'])).
% 6.48/6.73  thf('140', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X0))
% 6.48/6.73           = (k3_xboole_0 @ X1 @ X0))),
% 6.48/6.73      inference('demod', [status(thm)], ['132', '135'])).
% 6.48/6.73  thf('141', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 6.48/6.73           = (k3_xboole_0 @ X0 @ X0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['139', '140'])).
% 6.48/6.73  thf('142', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 6.48/6.73      inference('demod', [status(thm)], ['50', '51'])).
% 6.48/6.73  thf('143', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 6.48/6.73      inference('demod', [status(thm)], ['141', '142'])).
% 6.48/6.73  thf('144', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 6.48/6.73      inference('sup+', [status(thm)], ['138', '143'])).
% 6.48/6.73  thf('145', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 6.48/6.73      inference('sup+', [status(thm)], ['137', '144'])).
% 6.48/6.73  thf('146', plain,
% 6.48/6.73      (![X13 : $i, X14 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 6.48/6.73           = (k4_xboole_0 @ X13 @ X14))),
% 6.48/6.73      inference('cnf', [status(esa)], [t47_xboole_1])).
% 6.48/6.73  thf('147', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_B @ sk_B) = (k4_xboole_0 @ sk_B @ sk_C))),
% 6.48/6.73      inference('sup+', [status(thm)], ['145', '146'])).
% 6.48/6.73  thf('148', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['46', '47'])).
% 6.48/6.73  thf('149', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_C))),
% 6.48/6.73      inference('demod', [status(thm)], ['147', '148'])).
% 6.48/6.73  thf('150', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 6.48/6.73      inference('cnf', [status(esa)], [t3_boole])).
% 6.48/6.73  thf('151', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.48/6.73  thf('152', plain,
% 6.48/6.73      (((k2_xboole_0 @ sk_B @ sk_A)
% 6.48/6.73         = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 6.48/6.73      inference('demod', [status(thm)], ['126', '149', '150', '151'])).
% 6.48/6.73  thf('153', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 6.48/6.73           = (k4_xboole_0 @ X0 @ X1))),
% 6.48/6.73      inference('sup+', [status(thm)], ['39', '40'])).
% 6.48/6.73  thf('154', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_C)
% 6.48/6.73         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 6.48/6.73      inference('sup+', [status(thm)], ['152', '153'])).
% 6.48/6.73  thf('155', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_C) = (sk_D))),
% 6.48/6.73      inference('demod', [status(thm)], ['127', '128'])).
% 6.48/6.73  thf('156', plain,
% 6.48/6.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 6.48/6.73           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t41_xboole_1])).
% 6.48/6.73  thf('157', plain,
% 6.48/6.73      (((sk_D) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 6.48/6.73      inference('demod', [status(thm)], ['154', '155', '156'])).
% 6.48/6.73  thf('158', plain,
% 6.48/6.73      (![X15 : $i, X16 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 6.48/6.73           = (k3_xboole_0 @ X15 @ X16))),
% 6.48/6.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.48/6.73  thf('159', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_A @ sk_D)
% 6.48/6.73         = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['157', '158'])).
% 6.48/6.73  thf('160', plain,
% 6.48/6.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_C) = (sk_D))),
% 6.48/6.73      inference('demod', [status(thm)], ['127', '128'])).
% 6.48/6.73  thf('161', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['6', '7'])).
% 6.48/6.73  thf('162', plain,
% 6.48/6.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 6.48/6.73           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 6.48/6.73              (k3_xboole_0 @ X21 @ X23)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t52_xboole_1])).
% 6.48/6.73  thf('163', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 6.48/6.73           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['161', '162'])).
% 6.48/6.73  thf('164', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['133', '134'])).
% 6.48/6.73  thf('165', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 6.48/6.73           = (k3_xboole_0 @ X1 @ X0))),
% 6.48/6.73      inference('demod', [status(thm)], ['163', '164'])).
% 6.48/6.73  thf('166', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_A @ sk_D) = (k3_xboole_0 @ sk_A @ sk_C))),
% 6.48/6.73      inference('sup+', [status(thm)], ['160', '165'])).
% 6.48/6.73  thf('167', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 6.48/6.73      inference('demod', [status(thm)], ['94', '95'])).
% 6.48/6.73  thf('168', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 6.48/6.73      inference('demod', [status(thm)], ['141', '142'])).
% 6.48/6.73  thf('169', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 6.48/6.73      inference('sup+', [status(thm)], ['167', '168'])).
% 6.48/6.73  thf('170', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['46', '47'])).
% 6.48/6.73  thf('171', plain,
% 6.48/6.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 6.48/6.73           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 6.48/6.73              (k3_xboole_0 @ X21 @ X23)))),
% 6.48/6.73      inference('cnf', [status(esa)], [t52_xboole_1])).
% 6.48/6.73  thf('172', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['6', '7'])).
% 6.48/6.73  thf('173', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ 
% 6.48/6.73           (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))) = (k1_xboole_0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['171', '172'])).
% 6.48/6.73  thf('174', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) @ 
% 6.48/6.73           k1_xboole_0) = (k1_xboole_0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['170', '173'])).
% 6.48/6.73  thf('175', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 6.48/6.73      inference('cnf', [status(esa)], [t3_boole])).
% 6.48/6.73  thf('176', plain,
% 6.48/6.73      (![X0 : $i, X1 : $i]:
% 6.48/6.73         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 6.48/6.73      inference('demod', [status(thm)], ['174', '175'])).
% 6.48/6.73  thf('177', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 6.48/6.73      inference('sup+', [status(thm)], ['169', '176'])).
% 6.48/6.73  thf('178', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 6.48/6.73      inference('demod', [status(thm)], ['166', '177'])).
% 6.48/6.73  thf('179', plain,
% 6.48/6.73      (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 6.48/6.73      inference('demod', [status(thm)], ['159', '178'])).
% 6.48/6.73  thf('180', plain,
% 6.48/6.73      (![X13 : $i, X14 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 6.48/6.73           = (k4_xboole_0 @ X13 @ X14))),
% 6.48/6.73      inference('cnf', [status(esa)], [t47_xboole_1])).
% 6.48/6.73  thf('181', plain,
% 6.48/6.73      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 6.48/6.73         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 6.48/6.73      inference('sup+', [status(thm)], ['179', '180'])).
% 6.48/6.73  thf('182', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 6.48/6.73      inference('cnf', [status(esa)], [t3_boole])).
% 6.48/6.73  thf('183', plain,
% 6.48/6.73      (((sk_A) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 6.48/6.73      inference('demod', [status(thm)], ['181', '182'])).
% 6.48/6.73  thf('184', plain,
% 6.48/6.73      (((sk_D) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 6.48/6.73      inference('demod', [status(thm)], ['154', '155', '156'])).
% 6.48/6.73  thf('185', plain, (((sk_D) = (sk_A))),
% 6.48/6.73      inference('sup+', [status(thm)], ['183', '184'])).
% 6.48/6.73  thf('186', plain,
% 6.48/6.73      (![X6 : $i, X7 : $i]:
% 6.48/6.73         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 6.48/6.73           = (k4_xboole_0 @ X6 @ X7))),
% 6.48/6.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 6.48/6.73  thf('187', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 6.48/6.73      inference('demod', [status(thm)], ['34', '185', '186'])).
% 6.48/6.73  thf('188', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 6.48/6.73      inference('sup+', [status(thm)], ['138', '143'])).
% 6.48/6.73  thf('189', plain, (((sk_D) = (sk_A))),
% 6.48/6.73      inference('sup+', [status(thm)], ['183', '184'])).
% 6.48/6.73  thf('190', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 6.48/6.73      inference('demod', [status(thm)], ['188', '189'])).
% 6.48/6.73  thf('191', plain, (((sk_C) = (sk_B))),
% 6.48/6.73      inference('sup+', [status(thm)], ['187', '190'])).
% 6.48/6.73  thf('192', plain, (((sk_C) != (sk_B))),
% 6.48/6.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.48/6.73  thf('193', plain, ($false),
% 6.48/6.73      inference('simplify_reflect-', [status(thm)], ['191', '192'])).
% 6.48/6.73  
% 6.48/6.73  % SZS output end Refutation
% 6.48/6.73  
% 6.48/6.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
