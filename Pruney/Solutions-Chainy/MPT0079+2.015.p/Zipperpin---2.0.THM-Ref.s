%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dsnzgVseHd

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:58 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 170 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :   15
%              Number of atoms          :  618 (1229 expanded)
%              Number of equality atoms :   84 ( 169 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = sk_B ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['10','13'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['3','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','17'])).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','27','30','31','32'])).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('40',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('48',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('55',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('60',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = sk_C ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_B ) )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['55','64'])).

thf('66',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('69',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    sk_B = sk_C ),
    inference('sup+',[status(thm)],['37','69'])).

thf('71',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dsnzgVseHd
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:31:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.63  % Solved by: fo/fo7.sh
% 0.43/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.63  % done 213 iterations in 0.154s
% 0.43/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.63  % SZS output start Refutation
% 0.43/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.43/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.43/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.63  thf(t72_xboole_1, conjecture,
% 0.43/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.63     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.43/0.63         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.43/0.63       ( ( C ) = ( B ) ) ))).
% 0.43/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.63        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.43/0.63            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.43/0.63          ( ( C ) = ( B ) ) ) )),
% 0.43/0.63    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.43/0.63  thf('0', plain,
% 0.43/0.63      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(commutativity_k2_xboole_0, axiom,
% 0.43/0.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.43/0.63  thf('1', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.63  thf('2', plain,
% 0.43/0.63      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.43/0.63      inference('demod', [status(thm)], ['0', '1'])).
% 0.43/0.63  thf('3', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.63  thf('4', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(d7_xboole_0, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.43/0.63       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.63  thf('5', plain,
% 0.43/0.63      (![X4 : $i, X5 : $i]:
% 0.43/0.63         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.43/0.63      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.63  thf('6', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['4', '5'])).
% 0.43/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.43/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.43/0.63  thf('7', plain,
% 0.43/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.43/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.63  thf('8', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.43/0.63      inference('demod', [status(thm)], ['6', '7'])).
% 0.43/0.63  thf(t51_xboole_1, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.43/0.63       ( A ) ))).
% 0.43/0.63  thf('9', plain,
% 0.43/0.63      (![X20 : $i, X21 : $i]:
% 0.43/0.63         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.43/0.63           = (X20))),
% 0.43/0.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.43/0.63  thf('10', plain,
% 0.43/0.63      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_D)) = (sk_B))),
% 0.43/0.63      inference('sup+', [status(thm)], ['8', '9'])).
% 0.43/0.63  thf('11', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.63  thf(t1_boole, axiom,
% 0.43/0.63    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.63  thf('12', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.43/0.63      inference('cnf', [status(esa)], [t1_boole])).
% 0.43/0.63  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.43/0.63  thf('14', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 0.43/0.63      inference('demod', [status(thm)], ['10', '13'])).
% 0.43/0.63  thf(t41_xboole_1, axiom,
% 0.43/0.63    (![A:$i,B:$i,C:$i]:
% 0.43/0.63     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.43/0.63       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.43/0.63  thf('15', plain,
% 0.43/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.43/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.43/0.63           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.43/0.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.63  thf('16', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((k4_xboole_0 @ sk_B @ X0)
% 0.43/0.63           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_D @ X0)))),
% 0.43/0.63      inference('sup+', [status(thm)], ['14', '15'])).
% 0.43/0.63  thf('17', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((k4_xboole_0 @ sk_B @ X0)
% 0.43/0.63           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_D)))),
% 0.43/0.63      inference('sup+', [status(thm)], ['3', '16'])).
% 0.43/0.63  thf('18', plain,
% 0.43/0.63      (((k4_xboole_0 @ sk_B @ sk_C)
% 0.43/0.63         = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.43/0.63      inference('sup+', [status(thm)], ['2', '17'])).
% 0.43/0.63  thf('19', plain,
% 0.43/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.43/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.43/0.63           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.43/0.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.63  thf('20', plain,
% 0.43/0.63      (![X20 : $i, X21 : $i]:
% 0.43/0.63         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.43/0.63           = (X20))),
% 0.43/0.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.43/0.63  thf('21', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.63         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 0.43/0.63           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.43/0.63           = (k4_xboole_0 @ X2 @ X1))),
% 0.43/0.63      inference('sup+', [status(thm)], ['19', '20'])).
% 0.43/0.63  thf('22', plain,
% 0.43/0.63      (((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B) @ sk_A) @ 
% 0.43/0.63         (k4_xboole_0 @ sk_B @ sk_C)) = (k4_xboole_0 @ sk_B @ sk_B))),
% 0.43/0.63      inference('sup+', [status(thm)], ['18', '21'])).
% 0.43/0.63  thf(t3_boole, axiom,
% 0.43/0.63    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.63  thf('23', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.43/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.63  thf(t48_xboole_1, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.43/0.63  thf('24', plain,
% 0.43/0.63      (![X18 : $i, X19 : $i]:
% 0.43/0.63         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.43/0.63           = (k3_xboole_0 @ X18 @ X19))),
% 0.43/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.63  thf('25', plain,
% 0.43/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['23', '24'])).
% 0.43/0.63  thf(t2_boole, axiom,
% 0.43/0.63    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.43/0.63  thf('26', plain,
% 0.43/0.63      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.63      inference('cnf', [status(esa)], [t2_boole])).
% 0.43/0.63  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.63      inference('demod', [status(thm)], ['25', '26'])).
% 0.43/0.63  thf('28', plain,
% 0.43/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.43/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.63  thf('29', plain,
% 0.43/0.63      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.63      inference('cnf', [status(esa)], [t2_boole])).
% 0.43/0.63  thf('30', plain,
% 0.43/0.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['28', '29'])).
% 0.43/0.63  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.43/0.63  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.63      inference('demod', [status(thm)], ['25', '26'])).
% 0.43/0.63  thf('33', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.43/0.63      inference('demod', [status(thm)], ['22', '27', '30', '31', '32'])).
% 0.43/0.63  thf('34', plain,
% 0.43/0.63      (![X18 : $i, X19 : $i]:
% 0.43/0.63         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.43/0.63           = (k3_xboole_0 @ X18 @ X19))),
% 0.43/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.63  thf('35', plain,
% 0.43/0.63      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.43/0.63      inference('sup+', [status(thm)], ['33', '34'])).
% 0.43/0.63  thf('36', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.43/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.63  thf('37', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.43/0.63      inference('demod', [status(thm)], ['35', '36'])).
% 0.43/0.63  thf('38', plain,
% 0.43/0.63      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.43/0.63      inference('demod', [status(thm)], ['0', '1'])).
% 0.43/0.63  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.63      inference('demod', [status(thm)], ['25', '26'])).
% 0.43/0.63  thf('40', plain,
% 0.43/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.43/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.43/0.63           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.43/0.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.63  thf('41', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.43/0.63           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.43/0.63      inference('sup+', [status(thm)], ['39', '40'])).
% 0.43/0.63  thf('42', plain,
% 0.43/0.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['28', '29'])).
% 0.43/0.63  thf('43', plain,
% 0.43/0.63      (![X20 : $i, X21 : $i]:
% 0.43/0.63         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.43/0.63           = (X20))),
% 0.43/0.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.43/0.63  thf('44', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.43/0.63           = (k1_xboole_0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['42', '43'])).
% 0.43/0.63  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.43/0.63  thf('46', plain,
% 0.43/0.63      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.43/0.63      inference('demod', [status(thm)], ['44', '45'])).
% 0.43/0.63  thf('47', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.43/0.63      inference('demod', [status(thm)], ['41', '46'])).
% 0.43/0.63  thf('48', plain,
% 0.43/0.63      (((k1_xboole_0) = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.43/0.63      inference('sup+', [status(thm)], ['38', '47'])).
% 0.43/0.63  thf('49', plain,
% 0.43/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.43/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.43/0.63           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.43/0.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.63  thf(t39_xboole_1, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.63  thf('50', plain,
% 0.43/0.63      (![X9 : $i, X10 : $i]:
% 0.43/0.63         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.43/0.63           = (k2_xboole_0 @ X9 @ X10))),
% 0.43/0.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.43/0.63  thf('51', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.63         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.43/0.63           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.43/0.63      inference('sup+', [status(thm)], ['49', '50'])).
% 0.43/0.63  thf('52', plain,
% 0.43/0.63      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 0.43/0.63         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 0.43/0.63      inference('sup+', [status(thm)], ['48', '51'])).
% 0.43/0.63  thf('53', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.63  thf('54', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.43/0.63  thf('55', plain,
% 0.43/0.63      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 0.43/0.63      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.43/0.63  thf('56', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('57', plain,
% 0.43/0.63      (![X4 : $i, X5 : $i]:
% 0.43/0.63         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.43/0.63      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.63  thf('58', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['56', '57'])).
% 0.43/0.63  thf('59', plain,
% 0.43/0.63      (![X20 : $i, X21 : $i]:
% 0.43/0.63         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.43/0.63           = (X20))),
% 0.43/0.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.43/0.63  thf('60', plain,
% 0.43/0.63      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A)) = (sk_C))),
% 0.43/0.63      inference('sup+', [status(thm)], ['58', '59'])).
% 0.43/0.63  thf('61', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.43/0.63  thf('62', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.43/0.63      inference('demod', [status(thm)], ['60', '61'])).
% 0.43/0.63  thf('63', plain,
% 0.43/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.43/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.43/0.63           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.43/0.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.63  thf('64', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((k4_xboole_0 @ sk_C @ X0)
% 0.43/0.63           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.43/0.63      inference('sup+', [status(thm)], ['62', '63'])).
% 0.43/0.63  thf('65', plain,
% 0.43/0.63      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_B))
% 0.43/0.63         = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.43/0.63      inference('sup+', [status(thm)], ['55', '64'])).
% 0.43/0.63  thf('66', plain,
% 0.43/0.63      (![X18 : $i, X19 : $i]:
% 0.43/0.63         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.43/0.63           = (k3_xboole_0 @ X18 @ X19))),
% 0.43/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.63  thf('67', plain,
% 0.43/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.43/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.63  thf('68', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.43/0.63      inference('demod', [status(thm)], ['60', '61'])).
% 0.43/0.63  thf('69', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (sk_C))),
% 0.43/0.63      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.43/0.63  thf('70', plain, (((sk_B) = (sk_C))),
% 0.43/0.63      inference('sup+', [status(thm)], ['37', '69'])).
% 0.43/0.63  thf('71', plain, (((sk_C) != (sk_B))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('72', plain, ($false),
% 0.43/0.63      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.43/0.63  
% 0.43/0.63  % SZS output end Refutation
% 0.43/0.63  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
