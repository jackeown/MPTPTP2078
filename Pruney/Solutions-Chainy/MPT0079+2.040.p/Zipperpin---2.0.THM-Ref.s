%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6Y8JpoSeG6

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:02 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  174 (1411 expanded)
%              Number of leaves         :   21 ( 476 expanded)
%              Depth                    :   20
%              Number of atoms          : 1332 (11628 expanded)
%              Number of equality atoms :  164 (1464 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['2','17'])).

thf('19',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','16'])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('40',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','16'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('47',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','16'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('53',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('63',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('64',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_D @ sk_A ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('69',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('70',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('71',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('73',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_C @ sk_D ) )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('76',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('78',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('80',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('82',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('83',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('85',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('87',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('88',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('89',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('91',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('93',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('95',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('96',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('98',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_A ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('100',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','100'])).

thf('102',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('103',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('104',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['102','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('110',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('113',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['108','111','112'])).

thf('114',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('115',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('118',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','116','119'])).

thf('121',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['101','120'])).

thf('122',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('123',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('125',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('126',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('127',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['67','68','123','124','125','126'])).

thf('128',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['40','127'])).

thf('129',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('130',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('136',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['134','139'])).

thf('141',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup+',[status(thm)],['128','140'])).

thf('142',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('143',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['67','68','123','124','125','126'])).

thf('144',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('145',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['67','68','123','124','125','126'])).

thf('146',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('147',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['142','143','144','145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('149',plain,(
    sk_C = sk_B ),
    inference(demod,[status(thm)],['141','147','148'])).

thf('150',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['149','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6Y8JpoSeG6
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.65/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.84  % Solved by: fo/fo7.sh
% 0.65/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.84  % done 580 iterations in 0.387s
% 0.65/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.84  % SZS output start Refutation
% 0.65/0.84  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.65/0.84  thf(sk_D_type, type, sk_D: $i).
% 0.65/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.65/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.65/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.65/0.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.65/0.84  thf(t72_xboole_1, conjecture,
% 0.65/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.84     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.65/0.84         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.65/0.84       ( ( C ) = ( B ) ) ))).
% 0.65/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.84    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.84        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.65/0.84            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.65/0.84          ( ( C ) = ( B ) ) ) )),
% 0.65/0.84    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.65/0.84  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf(d7_xboole_0, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.65/0.84       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.65/0.84  thf('1', plain,
% 0.65/0.84      (![X2 : $i, X3 : $i]:
% 0.65/0.84         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.65/0.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.65/0.84  thf('2', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.65/0.84      inference('sup-', [status(thm)], ['0', '1'])).
% 0.65/0.84  thf(t48_xboole_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.65/0.84  thf('3', plain,
% 0.65/0.84      (![X15 : $i, X16 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.65/0.84           = (k3_xboole_0 @ X15 @ X16))),
% 0.65/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.84  thf('4', plain,
% 0.65/0.84      (![X15 : $i, X16 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.65/0.84           = (k3_xboole_0 @ X15 @ X16))),
% 0.65/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.84  thf('5', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.65/0.84           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['3', '4'])).
% 0.65/0.84  thf(t3_boole, axiom,
% 0.65/0.84    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.65/0.84  thf('6', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.65/0.84      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.84  thf('7', plain,
% 0.65/0.84      (![X15 : $i, X16 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.65/0.84           = (k3_xboole_0 @ X15 @ X16))),
% 0.65/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.84  thf('8', plain,
% 0.65/0.84      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.65/0.84      inference('sup+', [status(thm)], ['6', '7'])).
% 0.65/0.84  thf(t2_boole, axiom,
% 0.65/0.84    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.65/0.84  thf('9', plain,
% 0.65/0.84      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.65/0.84      inference('cnf', [status(esa)], [t2_boole])).
% 0.65/0.84  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.65/0.84      inference('demod', [status(thm)], ['8', '9'])).
% 0.65/0.84  thf('11', plain,
% 0.65/0.84      (![X15 : $i, X16 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.65/0.84           = (k3_xboole_0 @ X15 @ X16))),
% 0.65/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.84  thf('12', plain,
% 0.65/0.84      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.65/0.84      inference('sup+', [status(thm)], ['10', '11'])).
% 0.65/0.84  thf('13', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.65/0.84      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.84  thf('14', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.65/0.84      inference('demod', [status(thm)], ['12', '13'])).
% 0.65/0.84  thf(t49_xboole_1, axiom,
% 0.65/0.84    (![A:$i,B:$i,C:$i]:
% 0.65/0.84     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.65/0.84       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.65/0.84  thf('15', plain,
% 0.65/0.84      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.65/0.84         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.65/0.84           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.65/0.84      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.65/0.84  thf('16', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.65/0.84           = (k4_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('sup+', [status(thm)], ['14', '15'])).
% 0.65/0.84  thf('17', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.65/0.84           = (k4_xboole_0 @ X1 @ X0))),
% 0.65/0.84      inference('demod', [status(thm)], ['5', '16'])).
% 0.65/0.84  thf('18', plain,
% 0.65/0.84      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B))),
% 0.65/0.84      inference('sup+', [status(thm)], ['2', '17'])).
% 0.65/0.84  thf('19', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.65/0.84      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.84  thf('20', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 0.65/0.84      inference('demod', [status(thm)], ['18', '19'])).
% 0.65/0.84  thf('21', plain,
% 0.65/0.84      (![X15 : $i, X16 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.65/0.84           = (k3_xboole_0 @ X15 @ X16))),
% 0.65/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.84  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.65/0.84      inference('demod', [status(thm)], ['8', '9'])).
% 0.65/0.84  thf(commutativity_k2_xboole_0, axiom,
% 0.65/0.84    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.65/0.84  thf('23', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.65/0.84  thf(t41_xboole_1, axiom,
% 0.65/0.84    (![A:$i,B:$i,C:$i]:
% 0.65/0.84     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.65/0.84       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.65/0.84  thf('24', plain,
% 0.65/0.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.65/0.84           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.65/0.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.65/0.84  thf('25', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.65/0.84           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['23', '24'])).
% 0.65/0.84  thf('26', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1) @ X0)
% 0.65/0.84           = (k1_xboole_0))),
% 0.65/0.84      inference('sup+', [status(thm)], ['22', '25'])).
% 0.65/0.84  thf(t40_xboole_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.65/0.84  thf('27', plain,
% 0.65/0.84      (![X10 : $i, X11 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.65/0.84           = (k4_xboole_0 @ X10 @ X11))),
% 0.65/0.84      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.65/0.84  thf('28', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.65/0.84      inference('demod', [status(thm)], ['26', '27'])).
% 0.65/0.84  thf('29', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.65/0.84      inference('sup+', [status(thm)], ['21', '28'])).
% 0.65/0.84  thf('30', plain,
% 0.65/0.84      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.65/0.84         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.65/0.84           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.65/0.84      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.65/0.84  thf('31', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.65/0.84      inference('demod', [status(thm)], ['29', '30'])).
% 0.65/0.84  thf('32', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.65/0.84      inference('sup+', [status(thm)], ['20', '31'])).
% 0.65/0.84  thf('33', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.65/0.84           = (k4_xboole_0 @ X1 @ X0))),
% 0.65/0.84      inference('demod', [status(thm)], ['5', '16'])).
% 0.65/0.84  thf('34', plain,
% 0.65/0.84      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D))),
% 0.65/0.84      inference('sup+', [status(thm)], ['32', '33'])).
% 0.65/0.84  thf('35', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.65/0.84      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.84  thf('36', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_D))),
% 0.65/0.84      inference('demod', [status(thm)], ['34', '35'])).
% 0.65/0.84  thf('37', plain,
% 0.65/0.84      (![X15 : $i, X16 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.65/0.84           = (k3_xboole_0 @ X15 @ X16))),
% 0.65/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.84  thf('38', plain,
% 0.65/0.84      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_D))),
% 0.65/0.84      inference('sup+', [status(thm)], ['36', '37'])).
% 0.65/0.84  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.65/0.84      inference('demod', [status(thm)], ['8', '9'])).
% 0.65/0.84  thf('40', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_D))),
% 0.65/0.84      inference('demod', [status(thm)], ['38', '39'])).
% 0.65/0.84  thf('41', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('42', plain,
% 0.65/0.84      (![X2 : $i, X3 : $i]:
% 0.65/0.84         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.65/0.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.65/0.84  thf('43', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.65/0.84      inference('sup-', [status(thm)], ['41', '42'])).
% 0.65/0.84  thf('44', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.65/0.84           = (k4_xboole_0 @ X1 @ X0))),
% 0.65/0.84      inference('demod', [status(thm)], ['5', '16'])).
% 0.65/0.84  thf('45', plain,
% 0.65/0.84      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.65/0.84      inference('sup+', [status(thm)], ['43', '44'])).
% 0.65/0.84  thf('46', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.65/0.84      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.84  thf('47', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['45', '46'])).
% 0.65/0.84  thf('48', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.65/0.84      inference('demod', [status(thm)], ['29', '30'])).
% 0.65/0.84  thf('49', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.65/0.84      inference('sup+', [status(thm)], ['47', '48'])).
% 0.65/0.84  thf('50', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.65/0.84           = (k4_xboole_0 @ X1 @ X0))),
% 0.65/0.84      inference('demod', [status(thm)], ['5', '16'])).
% 0.65/0.84  thf('51', plain,
% 0.65/0.84      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.65/0.84      inference('sup+', [status(thm)], ['49', '50'])).
% 0.65/0.84  thf('52', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.65/0.84      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.84  thf('53', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.65/0.84      inference('demod', [status(thm)], ['51', '52'])).
% 0.65/0.84  thf('54', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('55', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.65/0.84  thf('56', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.65/0.84      inference('demod', [status(thm)], ['54', '55'])).
% 0.65/0.84  thf('57', plain,
% 0.65/0.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.65/0.84           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.65/0.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.65/0.84  thf('58', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 0.65/0.84           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['56', '57'])).
% 0.65/0.84  thf('59', plain,
% 0.65/0.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.65/0.84           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.65/0.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.65/0.84  thf('60', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 0.65/0.84           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['58', '59'])).
% 0.65/0.84  thf('61', plain,
% 0.65/0.84      (((k4_xboole_0 @ sk_A @ sk_D)
% 0.65/0.84         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.65/0.84      inference('sup+', [status(thm)], ['53', '60'])).
% 0.65/0.84  thf('62', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.65/0.84      inference('demod', [status(thm)], ['26', '27'])).
% 0.65/0.84  thf('63', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 0.65/0.84      inference('demod', [status(thm)], ['61', '62'])).
% 0.65/0.84  thf(t39_xboole_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.65/0.84  thf('64', plain,
% 0.65/0.84      (![X7 : $i, X8 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.65/0.84           = (k2_xboole_0 @ X7 @ X8))),
% 0.65/0.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.65/0.84  thf('65', plain,
% 0.65/0.84      (![X10 : $i, X11 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.65/0.84           = (k4_xboole_0 @ X10 @ X11))),
% 0.65/0.84      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.65/0.84  thf('66', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.65/0.84           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['64', '65'])).
% 0.65/0.84  thf('67', plain,
% 0.65/0.84      (((k4_xboole_0 @ (k2_xboole_0 @ sk_D @ sk_A) @ k1_xboole_0)
% 0.65/0.84         = (k4_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_A @ sk_D)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['63', '66'])).
% 0.65/0.84  thf('68', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.65/0.84  thf('69', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.65/0.84      inference('demod', [status(thm)], ['54', '55'])).
% 0.65/0.84  thf('70', plain,
% 0.65/0.84      (![X10 : $i, X11 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.65/0.84           = (k4_xboole_0 @ X10 @ X11))),
% 0.65/0.84      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.65/0.84  thf('71', plain,
% 0.65/0.84      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 0.65/0.84         = (k4_xboole_0 @ sk_C @ sk_D))),
% 0.65/0.84      inference('sup+', [status(thm)], ['69', '70'])).
% 0.65/0.84  thf('72', plain,
% 0.65/0.84      (![X7 : $i, X8 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.65/0.84           = (k2_xboole_0 @ X7 @ X8))),
% 0.65/0.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.65/0.84  thf('73', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_C @ sk_D))
% 0.65/0.84         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['71', '72'])).
% 0.65/0.84  thf('74', plain,
% 0.65/0.84      (![X7 : $i, X8 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.65/0.84           = (k2_xboole_0 @ X7 @ X8))),
% 0.65/0.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.65/0.84  thf('75', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.65/0.84  thf('76', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_C @ sk_D)
% 0.65/0.84         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.65/0.84      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.65/0.84  thf('77', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.65/0.84      inference('demod', [status(thm)], ['54', '55'])).
% 0.65/0.84  thf('78', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.65/0.84         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.65/0.84      inference('demod', [status(thm)], ['76', '77'])).
% 0.65/0.84  thf('79', plain,
% 0.65/0.84      (![X10 : $i, X11 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.65/0.84           = (k4_xboole_0 @ X10 @ X11))),
% 0.65/0.84      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.65/0.84  thf('80', plain,
% 0.65/0.84      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 0.65/0.84         (k2_xboole_0 @ sk_B @ sk_A))
% 0.65/0.84         = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['78', '79'])).
% 0.65/0.84  thf('81', plain,
% 0.65/0.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.65/0.84           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.65/0.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.65/0.84  thf('82', plain,
% 0.65/0.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.65/0.84           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.65/0.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.65/0.84  thf('83', plain,
% 0.65/0.84      (((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B) @ 
% 0.65/0.84         sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.65/0.84  thf('84', plain,
% 0.65/0.84      (![X7 : $i, X8 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.65/0.84           = (k2_xboole_0 @ X7 @ X8))),
% 0.65/0.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.65/0.84  thf('85', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_A @ 
% 0.65/0.84         (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A))
% 0.65/0.84         = (k2_xboole_0 @ sk_A @ 
% 0.65/0.84            (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['83', '84'])).
% 0.65/0.84  thf('86', plain,
% 0.65/0.84      (![X7 : $i, X8 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.65/0.84           = (k2_xboole_0 @ X7 @ X8))),
% 0.65/0.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.65/0.84  thf('87', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.65/0.84      inference('demod', [status(thm)], ['54', '55'])).
% 0.65/0.84  thf(t6_xboole_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.65/0.84  thf('88', plain,
% 0.65/0.84      (![X23 : $i, X24 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ X23 @ (k2_xboole_0 @ X23 @ X24))
% 0.65/0.84           = (k2_xboole_0 @ X23 @ X24))),
% 0.65/0.84      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.65/0.84  thf('89', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.65/0.84         = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.65/0.84      inference('sup+', [status(thm)], ['87', '88'])).
% 0.65/0.84  thf('90', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.65/0.84      inference('demod', [status(thm)], ['54', '55'])).
% 0.65/0.84  thf('91', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.65/0.84         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['89', '90'])).
% 0.65/0.84  thf('92', plain,
% 0.65/0.84      (![X10 : $i, X11 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.65/0.84           = (k4_xboole_0 @ X10 @ X11))),
% 0.65/0.84      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.65/0.84  thf('93', plain,
% 0.65/0.84      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 0.65/0.84         (k2_xboole_0 @ sk_B @ sk_A))
% 0.65/0.84         = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['91', '92'])).
% 0.65/0.84  thf('94', plain,
% 0.65/0.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.65/0.84           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.65/0.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.65/0.84  thf('95', plain,
% 0.65/0.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.65/0.84           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.65/0.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.65/0.84  thf('96', plain,
% 0.65/0.84      (((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B) @ 
% 0.65/0.84         sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.65/0.84  thf('97', plain,
% 0.65/0.84      (![X7 : $i, X8 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.65/0.84           = (k2_xboole_0 @ X7 @ X8))),
% 0.65/0.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.65/0.84  thf('98', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_A @ 
% 0.65/0.84         (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_A))
% 0.65/0.84         = (k2_xboole_0 @ sk_A @ 
% 0.65/0.84            (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['96', '97'])).
% 0.65/0.84  thf('99', plain,
% 0.65/0.84      (![X7 : $i, X8 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.65/0.84           = (k2_xboole_0 @ X7 @ X8))),
% 0.65/0.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.65/0.84  thf('100', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B))
% 0.65/0.84         = (k2_xboole_0 @ sk_A @ 
% 0.65/0.84            (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B)))),
% 0.65/0.84      inference('demod', [status(thm)], ['98', '99'])).
% 0.65/0.84  thf('101', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B))
% 0.65/0.84         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 0.65/0.84      inference('demod', [status(thm)], ['85', '86', '100'])).
% 0.65/0.84  thf('102', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.65/0.84         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['89', '90'])).
% 0.65/0.84  thf('103', plain,
% 0.65/0.84      (![X10 : $i, X11 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.65/0.84           = (k4_xboole_0 @ X10 @ X11))),
% 0.65/0.84      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.65/0.84  thf('104', plain,
% 0.65/0.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.65/0.84           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.65/0.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.65/0.84  thf('105', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ 
% 0.65/0.84           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1) @ 
% 0.65/0.84           X0) = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['103', '104'])).
% 0.65/0.84  thf('106', plain,
% 0.65/0.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.65/0.84           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.65/0.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.65/0.84  thf('107', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ 
% 0.65/0.84           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1) @ 
% 0.65/0.84           X0) = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.65/0.84      inference('demod', [status(thm)], ['105', '106'])).
% 0.65/0.84  thf('108', plain,
% 0.65/0.84      (((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B) @ 
% 0.65/0.84         sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.65/0.84      inference('sup+', [status(thm)], ['102', '107'])).
% 0.65/0.84  thf('109', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.65/0.84  thf('110', plain,
% 0.65/0.84      (![X10 : $i, X11 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.65/0.84           = (k4_xboole_0 @ X10 @ X11))),
% 0.65/0.84      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.65/0.84  thf('111', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.65/0.84           = (k4_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('sup+', [status(thm)], ['109', '110'])).
% 0.65/0.84  thf('112', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.65/0.84      inference('demod', [status(thm)], ['26', '27'])).
% 0.65/0.84  thf('113', plain,
% 0.65/0.84      (((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['108', '111', '112'])).
% 0.65/0.84  thf('114', plain,
% 0.65/0.84      (![X7 : $i, X8 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.65/0.84           = (k2_xboole_0 @ X7 @ X8))),
% 0.65/0.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.65/0.84  thf('115', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 0.65/0.84         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['113', '114'])).
% 0.65/0.84  thf('116', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.65/0.84  thf('117', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.65/0.84  thf(t1_boole, axiom,
% 0.65/0.84    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.65/0.84  thf('118', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.65/0.84      inference('cnf', [status(esa)], [t1_boole])).
% 0.65/0.84  thf('119', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.65/0.84      inference('sup+', [status(thm)], ['117', '118'])).
% 0.65/0.84  thf('120', plain,
% 0.65/0.84      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 0.65/0.84      inference('demod', [status(thm)], ['115', '116', '119'])).
% 0.65/0.84  thf('121', plain,
% 0.65/0.84      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['101', '120'])).
% 0.65/0.84  thf('122', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 0.65/0.84      inference('demod', [status(thm)], ['18', '19'])).
% 0.65/0.84  thf('123', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['121', '122'])).
% 0.65/0.84  thf('124', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.65/0.84      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.84  thf('125', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 0.65/0.84      inference('demod', [status(thm)], ['61', '62'])).
% 0.65/0.84  thf('126', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.65/0.84      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.84  thf('127', plain, (((sk_A) = (sk_D))),
% 0.65/0.84      inference('demod', [status(thm)],
% 0.65/0.84                ['67', '68', '123', '124', '125', '126'])).
% 0.65/0.84  thf('128', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['40', '127'])).
% 0.65/0.84  thf('129', plain,
% 0.65/0.84      (![X15 : $i, X16 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.65/0.84           = (k3_xboole_0 @ X15 @ X16))),
% 0.65/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.84  thf('130', plain,
% 0.65/0.84      (![X7 : $i, X8 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.65/0.84           = (k2_xboole_0 @ X7 @ X8))),
% 0.65/0.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.65/0.84  thf('131', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.65/0.84           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.65/0.84      inference('sup+', [status(thm)], ['129', '130'])).
% 0.65/0.84  thf('132', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.65/0.84  thf('133', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.65/0.84  thf('134', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.65/0.84           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.65/0.84  thf('135', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.65/0.84      inference('demod', [status(thm)], ['26', '27'])).
% 0.65/0.84  thf('136', plain,
% 0.65/0.84      (![X7 : $i, X8 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.65/0.84           = (k2_xboole_0 @ X7 @ X8))),
% 0.65/0.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.65/0.84  thf('137', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.65/0.84           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['135', '136'])).
% 0.65/0.84  thf('138', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.65/0.84      inference('cnf', [status(esa)], [t1_boole])).
% 0.65/0.84  thf('139', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['137', '138'])).
% 0.65/0.84  thf('140', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.65/0.84           = (X1))),
% 0.65/0.84      inference('demod', [status(thm)], ['134', '139'])).
% 0.65/0.84  thf('141', plain,
% 0.65/0.84      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 0.65/0.84      inference('sup+', [status(thm)], ['128', '140'])).
% 0.65/0.84  thf('142', plain,
% 0.65/0.84      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 0.65/0.84         = (k4_xboole_0 @ sk_C @ sk_D))),
% 0.65/0.84      inference('sup+', [status(thm)], ['69', '70'])).
% 0.65/0.84  thf('143', plain, (((sk_A) = (sk_D))),
% 0.65/0.84      inference('demod', [status(thm)],
% 0.65/0.84                ['67', '68', '123', '124', '125', '126'])).
% 0.65/0.84  thf('144', plain,
% 0.65/0.84      (![X10 : $i, X11 : $i]:
% 0.65/0.84         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.65/0.84           = (k4_xboole_0 @ X10 @ X11))),
% 0.65/0.84      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.65/0.84  thf('145', plain, (((sk_A) = (sk_D))),
% 0.65/0.84      inference('demod', [status(thm)],
% 0.65/0.84                ['67', '68', '123', '124', '125', '126'])).
% 0.65/0.84  thf('146', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['45', '46'])).
% 0.65/0.84  thf('147', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 0.65/0.84      inference('demod', [status(thm)], ['142', '143', '144', '145', '146'])).
% 0.65/0.84  thf('148', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.65/0.84      inference('sup+', [status(thm)], ['117', '118'])).
% 0.65/0.84  thf('149', plain, (((sk_C) = (sk_B))),
% 0.65/0.84      inference('demod', [status(thm)], ['141', '147', '148'])).
% 0.65/0.84  thf('150', plain, (((sk_C) != (sk_B))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('151', plain, ($false),
% 0.65/0.84      inference('simplify_reflect-', [status(thm)], ['149', '150'])).
% 0.65/0.84  
% 0.65/0.84  % SZS output end Refutation
% 0.65/0.84  
% 0.68/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
