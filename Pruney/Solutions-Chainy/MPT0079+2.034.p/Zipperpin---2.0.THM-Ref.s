%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VWyr0QZZLj

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:01 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 539 expanded)
%              Number of leaves         :   22 ( 187 expanded)
%              Depth                    :   17
%              Number of atoms          :  739 (4198 expanded)
%              Number of equality atoms :   97 ( 541 expanded)
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

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_A ),
    inference('sup+',[status(thm)],['9','10'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k2_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('42',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','43','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['23','45'])).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('52',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','43','44'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('55',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('60',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_D ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('65',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('68',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['52','68'])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','69'])).

thf('71',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('72',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('74',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('75',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['52','68'])).

thf('77',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('78',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['52','68'])).

thf('79',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('81',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('83',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = sk_C ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('85',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['75','76','77','78','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('88',plain,(
    sk_C = sk_B ),
    inference(demod,[status(thm)],['72','86','87'])).

thf('89',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VWyr0QZZLj
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:48:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.61/1.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.61/1.80  % Solved by: fo/fo7.sh
% 1.61/1.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.61/1.80  % done 674 iterations in 1.338s
% 1.61/1.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.61/1.80  % SZS output start Refutation
% 1.61/1.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.61/1.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.61/1.80  thf(sk_A_type, type, sk_A: $i).
% 1.61/1.80  thf(sk_C_type, type, sk_C: $i).
% 1.61/1.80  thf(sk_D_type, type, sk_D: $i).
% 1.61/1.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.61/1.80  thf(sk_B_type, type, sk_B: $i).
% 1.61/1.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.61/1.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.61/1.80  thf(t72_xboole_1, conjecture,
% 1.61/1.80    (![A:$i,B:$i,C:$i,D:$i]:
% 1.61/1.80     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.61/1.80         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.61/1.80       ( ( C ) = ( B ) ) ))).
% 1.61/1.80  thf(zf_stmt_0, negated_conjecture,
% 1.61/1.80    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.61/1.80        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.61/1.80            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.61/1.80          ( ( C ) = ( B ) ) ) )),
% 1.61/1.80    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 1.61/1.80  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf(symmetry_r1_xboole_0, axiom,
% 1.61/1.80    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.61/1.80  thf('1', plain,
% 1.61/1.80      (![X5 : $i, X6 : $i]:
% 1.61/1.80         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.61/1.80      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.61/1.80  thf('2', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 1.61/1.80      inference('sup-', [status(thm)], ['0', '1'])).
% 1.61/1.80  thf(d7_xboole_0, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.61/1.80       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.61/1.80  thf('3', plain,
% 1.61/1.80      (![X2 : $i, X3 : $i]:
% 1.61/1.80         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.61/1.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.61/1.80  thf('4', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['2', '3'])).
% 1.61/1.80  thf('5', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('6', plain,
% 1.61/1.80      (![X5 : $i, X6 : $i]:
% 1.61/1.80         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.61/1.80      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.61/1.80  thf('7', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 1.61/1.80      inference('sup-', [status(thm)], ['5', '6'])).
% 1.61/1.80  thf('8', plain,
% 1.61/1.80      (![X2 : $i, X3 : $i]:
% 1.61/1.80         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.61/1.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.61/1.80  thf('9', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['7', '8'])).
% 1.61/1.80  thf(t51_xboole_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.61/1.80       ( A ) ))).
% 1.61/1.80  thf('10', plain,
% 1.61/1.80      (![X22 : $i, X23 : $i]:
% 1.61/1.80         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 1.61/1.80           = (X22))),
% 1.61/1.80      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.61/1.80  thf('11', plain,
% 1.61/1.80      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_A))),
% 1.61/1.80      inference('sup+', [status(thm)], ['9', '10'])).
% 1.61/1.80  thf(commutativity_k2_xboole_0, axiom,
% 1.61/1.80    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.61/1.80  thf('12', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.61/1.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.61/1.80  thf(t1_boole, axiom,
% 1.61/1.80    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.61/1.80  thf('13', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.61/1.80      inference('cnf', [status(esa)], [t1_boole])).
% 1.61/1.80  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['12', '13'])).
% 1.61/1.80  thf('15', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 1.61/1.80      inference('demod', [status(thm)], ['11', '14'])).
% 1.61/1.80  thf('16', plain,
% 1.61/1.80      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('17', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.61/1.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.61/1.80  thf('18', plain,
% 1.61/1.80      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.61/1.80      inference('demod', [status(thm)], ['16', '17'])).
% 1.61/1.80  thf(t41_xboole_1, axiom,
% 1.61/1.80    (![A:$i,B:$i,C:$i]:
% 1.61/1.80     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.61/1.80       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.61/1.80  thf('19', plain,
% 1.61/1.80      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.61/1.80         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 1.61/1.80           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 1.61/1.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.61/1.80  thf('20', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 1.61/1.80           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.61/1.80      inference('sup+', [status(thm)], ['18', '19'])).
% 1.61/1.80  thf('21', plain,
% 1.61/1.80      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.61/1.80         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 1.61/1.80           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 1.61/1.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.61/1.80  thf('22', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 1.61/1.80           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 1.61/1.80      inference('demod', [status(thm)], ['20', '21'])).
% 1.61/1.80  thf('23', plain,
% 1.61/1.80      (((k4_xboole_0 @ sk_A @ sk_D)
% 1.61/1.80         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 1.61/1.80      inference('sup+', [status(thm)], ['15', '22'])).
% 1.61/1.80  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['12', '13'])).
% 1.61/1.80  thf(t40_xboole_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.61/1.80  thf('25', plain,
% 1.61/1.80      (![X12 : $i, X13 : $i]:
% 1.61/1.80         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 1.61/1.80           = (k4_xboole_0 @ X12 @ X13))),
% 1.61/1.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.61/1.80  thf(t39_xboole_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.61/1.80  thf('26', plain,
% 1.61/1.80      (![X9 : $i, X10 : $i]:
% 1.61/1.80         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 1.61/1.80           = (k2_xboole_0 @ X9 @ X10))),
% 1.61/1.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.61/1.80  thf('27', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.61/1.80           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.61/1.80      inference('sup+', [status(thm)], ['25', '26'])).
% 1.61/1.80  thf('28', plain,
% 1.61/1.80      (![X9 : $i, X10 : $i]:
% 1.61/1.80         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 1.61/1.80           = (k2_xboole_0 @ X9 @ X10))),
% 1.61/1.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.61/1.80  thf('29', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         ((k2_xboole_0 @ X0 @ X1)
% 1.61/1.80           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.61/1.80      inference('demod', [status(thm)], ['27', '28'])).
% 1.61/1.80  thf('30', plain,
% 1.61/1.80      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['24', '29'])).
% 1.61/1.80  thf('31', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.61/1.80      inference('cnf', [status(esa)], [t1_boole])).
% 1.61/1.80  thf('32', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.61/1.80      inference('demod', [status(thm)], ['30', '31'])).
% 1.61/1.80  thf(t4_xboole_1, axiom,
% 1.61/1.80    (![A:$i,B:$i,C:$i]:
% 1.61/1.80     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.61/1.80       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.61/1.80  thf('33', plain,
% 1.61/1.80      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.61/1.80         ((k2_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X21)
% 1.61/1.80           = (k2_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 1.61/1.80      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.61/1.80  thf('34', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.61/1.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.61/1.80  thf('35', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.80         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 1.61/1.80           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.61/1.80      inference('sup+', [status(thm)], ['33', '34'])).
% 1.61/1.80  thf('36', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.61/1.80           = (k2_xboole_0 @ X1 @ X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['32', '35'])).
% 1.61/1.80  thf('37', plain,
% 1.61/1.80      (![X12 : $i, X13 : $i]:
% 1.61/1.80         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 1.61/1.80           = (k4_xboole_0 @ X12 @ X13))),
% 1.61/1.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.61/1.80  thf('38', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 1.61/1.80           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.61/1.80      inference('sup+', [status(thm)], ['36', '37'])).
% 1.61/1.80  thf(t3_boole, axiom,
% 1.61/1.80    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.61/1.80  thf('39', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 1.61/1.80      inference('cnf', [status(esa)], [t3_boole])).
% 1.61/1.80  thf(t48_xboole_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.61/1.80  thf('40', plain,
% 1.61/1.80      (![X17 : $i, X18 : $i]:
% 1.61/1.80         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.61/1.80           = (k3_xboole_0 @ X17 @ X18))),
% 1.61/1.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.61/1.80  thf('41', plain,
% 1.61/1.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['39', '40'])).
% 1.61/1.80  thf(t2_boole, axiom,
% 1.61/1.80    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.61/1.80  thf('42', plain,
% 1.61/1.80      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.80      inference('cnf', [status(esa)], [t2_boole])).
% 1.61/1.80  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['41', '42'])).
% 1.61/1.80  thf('44', plain,
% 1.61/1.80      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.61/1.80         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 1.61/1.80           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 1.61/1.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.61/1.80  thf('45', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.61/1.80      inference('demod', [status(thm)], ['38', '43', '44'])).
% 1.61/1.80  thf('46', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['23', '45'])).
% 1.61/1.80  thf('47', plain,
% 1.61/1.80      (![X9 : $i, X10 : $i]:
% 1.61/1.80         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 1.61/1.80           = (k2_xboole_0 @ X9 @ X10))),
% 1.61/1.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.61/1.80  thf('48', plain,
% 1.61/1.80      (((k2_xboole_0 @ sk_D @ k1_xboole_0) = (k2_xboole_0 @ sk_D @ sk_A))),
% 1.61/1.80      inference('sup+', [status(thm)], ['46', '47'])).
% 1.61/1.80  thf('49', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.61/1.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.61/1.80  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['12', '13'])).
% 1.61/1.80  thf('51', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.61/1.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.61/1.80  thf('52', plain, (((sk_D) = (k2_xboole_0 @ sk_A @ sk_D))),
% 1.61/1.80      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 1.61/1.80  thf('53', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.61/1.80      inference('demod', [status(thm)], ['38', '43', '44'])).
% 1.61/1.80  thf('54', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 1.61/1.80           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 1.61/1.80      inference('demod', [status(thm)], ['20', '21'])).
% 1.61/1.80  thf('55', plain,
% 1.61/1.80      (((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A))),
% 1.61/1.80      inference('sup+', [status(thm)], ['53', '54'])).
% 1.61/1.80  thf('56', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('57', plain,
% 1.61/1.80      (![X2 : $i, X3 : $i]:
% 1.61/1.80         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.61/1.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.61/1.80  thf('58', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['56', '57'])).
% 1.61/1.80  thf('59', plain,
% 1.61/1.80      (![X22 : $i, X23 : $i]:
% 1.61/1.80         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 1.61/1.80           = (X22))),
% 1.61/1.80      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.61/1.80  thf('60', plain,
% 1.61/1.80      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_D))),
% 1.61/1.80      inference('sup+', [status(thm)], ['58', '59'])).
% 1.61/1.80  thf('61', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['12', '13'])).
% 1.61/1.80  thf('62', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 1.61/1.80      inference('demod', [status(thm)], ['60', '61'])).
% 1.61/1.80  thf('63', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 1.61/1.80      inference('demod', [status(thm)], ['55', '62'])).
% 1.61/1.80  thf('64', plain,
% 1.61/1.80      (![X9 : $i, X10 : $i]:
% 1.61/1.80         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 1.61/1.80           = (k2_xboole_0 @ X9 @ X10))),
% 1.61/1.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.61/1.80  thf('65', plain,
% 1.61/1.80      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_D))),
% 1.61/1.80      inference('sup+', [status(thm)], ['63', '64'])).
% 1.61/1.80  thf('66', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.61/1.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.61/1.80  thf('67', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['12', '13'])).
% 1.61/1.80  thf('68', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 1.61/1.80      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.61/1.80  thf('69', plain, (((sk_A) = (sk_D))),
% 1.61/1.80      inference('sup+', [status(thm)], ['52', '68'])).
% 1.61/1.80  thf('70', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['4', '69'])).
% 1.61/1.80  thf('71', plain,
% 1.61/1.80      (![X22 : $i, X23 : $i]:
% 1.61/1.80         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 1.61/1.80           = (X22))),
% 1.61/1.80      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.61/1.80  thf('72', plain,
% 1.61/1.80      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 1.61/1.80      inference('sup+', [status(thm)], ['70', '71'])).
% 1.61/1.80  thf('73', plain,
% 1.61/1.80      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.61/1.80      inference('demod', [status(thm)], ['16', '17'])).
% 1.61/1.80  thf('74', plain,
% 1.61/1.80      (![X12 : $i, X13 : $i]:
% 1.61/1.80         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 1.61/1.80           = (k4_xboole_0 @ X12 @ X13))),
% 1.61/1.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.61/1.80  thf('75', plain,
% 1.61/1.80      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 1.61/1.80         = (k4_xboole_0 @ sk_C @ sk_D))),
% 1.61/1.80      inference('sup+', [status(thm)], ['73', '74'])).
% 1.61/1.80  thf('76', plain, (((sk_A) = (sk_D))),
% 1.61/1.80      inference('sup+', [status(thm)], ['52', '68'])).
% 1.61/1.80  thf('77', plain,
% 1.61/1.80      (![X12 : $i, X13 : $i]:
% 1.61/1.80         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 1.61/1.80           = (k4_xboole_0 @ X12 @ X13))),
% 1.61/1.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.61/1.80  thf('78', plain, (((sk_A) = (sk_D))),
% 1.61/1.80      inference('sup+', [status(thm)], ['52', '68'])).
% 1.61/1.80  thf('79', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('80', plain,
% 1.61/1.80      (![X2 : $i, X3 : $i]:
% 1.61/1.80         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.61/1.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.61/1.80  thf('81', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['79', '80'])).
% 1.61/1.80  thf('82', plain,
% 1.61/1.80      (![X22 : $i, X23 : $i]:
% 1.61/1.80         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 1.61/1.80           = (X22))),
% 1.61/1.80      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.61/1.80  thf('83', plain,
% 1.61/1.80      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A)) = (sk_C))),
% 1.61/1.80      inference('sup+', [status(thm)], ['81', '82'])).
% 1.61/1.80  thf('84', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['12', '13'])).
% 1.61/1.80  thf('85', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 1.61/1.80      inference('demod', [status(thm)], ['83', '84'])).
% 1.61/1.80  thf('86', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 1.61/1.80      inference('demod', [status(thm)], ['75', '76', '77', '78', '85'])).
% 1.61/1.80  thf('87', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.61/1.80      inference('sup+', [status(thm)], ['12', '13'])).
% 1.61/1.80  thf('88', plain, (((sk_C) = (sk_B))),
% 1.61/1.80      inference('demod', [status(thm)], ['72', '86', '87'])).
% 1.61/1.80  thf('89', plain, (((sk_C) != (sk_B))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('90', plain, ($false),
% 1.61/1.80      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 1.61/1.80  
% 1.61/1.80  % SZS output end Refutation
% 1.61/1.80  
% 1.65/1.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
