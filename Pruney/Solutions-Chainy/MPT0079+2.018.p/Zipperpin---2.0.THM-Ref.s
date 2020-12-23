%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UwdcgGgyTQ

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:59 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 623 expanded)
%              Number of leaves         :   18 ( 214 expanded)
%              Depth                    :   19
%              Number of atoms          :  897 (4716 expanded)
%              Number of equality atoms :  119 ( 637 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['2','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('31',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','34','35'])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('39',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('47',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['38','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','20','21'])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['36','53'])).

thf('55',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('60',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('64',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('66',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('68',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('70',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('72',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('83',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','81','82'])).

thf('84',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('85',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('86',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('90',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('92',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('94',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('97',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('98',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['92','95','96','97'])).

thf('99',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['83','98'])).

thf('100',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('101',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['58','99','100'])).

thf('102',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['83','98'])).

thf('103',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('104',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('106',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    sk_B = sk_C ),
    inference('sup+',[status(thm)],['101','106'])).

thf('108',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UwdcgGgyTQ
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:15:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.52/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.73  % Solved by: fo/fo7.sh
% 0.52/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.73  % done 458 iterations in 0.266s
% 0.52/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.73  % SZS output start Refutation
% 0.52/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.73  thf(t72_xboole_1, conjecture,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.52/0.73         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.52/0.73       ( ( C ) = ( B ) ) ))).
% 0.52/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.73    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.52/0.73            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.52/0.73          ( ( C ) = ( B ) ) ) )),
% 0.52/0.73    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.52/0.73  thf('0', plain,
% 0.52/0.73      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(commutativity_k2_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.52/0.73  thf('1', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('2', plain,
% 0.52/0.73      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['0', '1'])).
% 0.52/0.73  thf(t40_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.52/0.73  thf('3', plain,
% 0.52/0.73      (![X8 : $i, X9 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 0.52/0.73           = (k4_xboole_0 @ X8 @ X9))),
% 0.52/0.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.52/0.73  thf(t3_boole, axiom,
% 0.52/0.73    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.73  thf('4', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.73  thf('5', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['3', '4'])).
% 0.52/0.73  thf('6', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.73  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['5', '6'])).
% 0.52/0.73  thf('8', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['7', '8'])).
% 0.52/0.73  thf('10', plain,
% 0.52/0.73      (![X8 : $i, X9 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 0.52/0.73           = (k4_xboole_0 @ X8 @ X9))),
% 0.52/0.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.52/0.73  thf('11', plain,
% 0.52/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['9', '10'])).
% 0.52/0.73  thf(t41_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.52/0.73       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.52/0.73  thf('12', plain,
% 0.52/0.73      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.52/0.73           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.73  thf('13', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.52/0.73           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['11', '12'])).
% 0.52/0.73  thf('14', plain,
% 0.52/0.73      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.52/0.73           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.73  thf('15', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.52/0.73           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.52/0.73      inference('demod', [status(thm)], ['13', '14'])).
% 0.52/0.73  thf('16', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.73  thf(t48_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.73  thf('17', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.52/0.73           = (k3_xboole_0 @ X15 @ X16))),
% 0.52/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.73  thf('18', plain,
% 0.52/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['16', '17'])).
% 0.52/0.73  thf('19', plain,
% 0.52/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['9', '10'])).
% 0.52/0.73  thf('20', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['18', '19'])).
% 0.52/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.52/0.73  thf('21', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('22', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.52/0.73           = (k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.52/0.73      inference('demod', [status(thm)], ['15', '20', '21'])).
% 0.52/0.73  thf('23', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.52/0.73         = (k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['2', '22'])).
% 0.52/0.73  thf('24', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('25', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(d7_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.52/0.73       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.73  thf('26', plain,
% 0.52/0.73      (![X4 : $i, X5 : $i]:
% 0.52/0.73         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.52/0.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.52/0.73  thf('27', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.52/0.73  thf(t47_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.52/0.73  thf('28', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 0.52/0.73           = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.73  thf('29', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.52/0.73      inference('sup+', [status(thm)], ['27', '28'])).
% 0.52/0.73  thf('30', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.73  thf('31', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.52/0.73      inference('demod', [status(thm)], ['29', '30'])).
% 0.52/0.73  thf('32', plain,
% 0.52/0.73      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.52/0.73           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.73  thf('33', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ sk_C @ X0)
% 0.52/0.73           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['31', '32'])).
% 0.52/0.73  thf('34', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ sk_C @ X0)
% 0.52/0.73           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ X0 @ sk_A)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['24', '33'])).
% 0.52/0.73  thf('35', plain,
% 0.52/0.73      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['0', '1'])).
% 0.52/0.73  thf('36', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_C @ sk_B)
% 0.52/0.73         = (k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['23', '34', '35'])).
% 0.52/0.73  thf('37', plain,
% 0.52/0.73      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['0', '1'])).
% 0.52/0.73  thf('38', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('39', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('40', plain,
% 0.52/0.73      (![X4 : $i, X5 : $i]:
% 0.52/0.73         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.52/0.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.52/0.73  thf('41', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['39', '40'])).
% 0.52/0.73  thf('42', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('43', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['41', '42'])).
% 0.52/0.73  thf('44', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 0.52/0.73           = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.73  thf('45', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D))),
% 0.52/0.73      inference('sup+', [status(thm)], ['43', '44'])).
% 0.52/0.73  thf('46', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.73  thf('47', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['45', '46'])).
% 0.52/0.73  thf('48', plain,
% 0.52/0.73      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.52/0.73           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.73  thf('49', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ sk_B @ X0)
% 0.52/0.73           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_D @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['47', '48'])).
% 0.52/0.73  thf('50', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ sk_B @ X0)
% 0.52/0.73           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_D)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['38', '49'])).
% 0.52/0.73  thf('51', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_B @ sk_C)
% 0.52/0.73         = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['37', '50'])).
% 0.52/0.73  thf('52', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.52/0.73           = (k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.52/0.73      inference('demod', [status(thm)], ['15', '20', '21'])).
% 0.52/0.73  thf('53', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_B @ sk_C)
% 0.52/0.73         = (k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['51', '52'])).
% 0.52/0.73  thf('54', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_B @ sk_C) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.52/0.73      inference('sup+', [status(thm)], ['36', '53'])).
% 0.52/0.73  thf('55', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.52/0.73           = (k3_xboole_0 @ X15 @ X16))),
% 0.52/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.73  thf('56', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.52/0.73         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.52/0.73      inference('sup+', [status(thm)], ['54', '55'])).
% 0.52/0.73  thf('57', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('58', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.52/0.73         = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.52/0.73      inference('demod', [status(thm)], ['56', '57'])).
% 0.52/0.73  thf('59', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_B @ sk_C)
% 0.52/0.73         = (k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['51', '52'])).
% 0.52/0.73  thf('60', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['45', '46'])).
% 0.52/0.73  thf('61', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.52/0.73           = (k3_xboole_0 @ X15 @ X16))),
% 0.52/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.73  thf('62', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_D))),
% 0.52/0.73      inference('sup+', [status(thm)], ['60', '61'])).
% 0.52/0.73  thf('63', plain,
% 0.52/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['9', '10'])).
% 0.52/0.73  thf('64', plain,
% 0.52/0.73      (((k4_xboole_0 @ k1_xboole_0 @ sk_B) = (k3_xboole_0 @ sk_B @ sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['62', '63'])).
% 0.52/0.73  thf('65', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['41', '42'])).
% 0.52/0.73  thf('66', plain, (((k4_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['64', '65'])).
% 0.52/0.73  thf('67', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.52/0.73           = (k3_xboole_0 @ X15 @ X16))),
% 0.52/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.73  thf('68', plain,
% 0.52/0.73      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.52/0.73         = (k3_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.52/0.73      inference('sup+', [status(thm)], ['66', '67'])).
% 0.52/0.73  thf('69', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.73  thf('70', plain, (((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['68', '69'])).
% 0.52/0.73  thf('71', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 0.52/0.73           = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.73  thf('72', plain,
% 0.52/0.73      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.52/0.73           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.73  thf('73', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.52/0.73           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['71', '72'])).
% 0.52/0.73  thf('74', plain,
% 0.52/0.73      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.52/0.73           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.73  thf('75', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 0.52/0.73           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 0.52/0.73      inference('demod', [status(thm)], ['73', '74'])).
% 0.52/0.73  thf('76', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ X0))
% 0.52/0.73           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['70', '75'])).
% 0.52/0.73  thf('77', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['18', '19'])).
% 0.52/0.73  thf('78', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('79', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['7', '8'])).
% 0.52/0.73  thf('80', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['18', '19'])).
% 0.52/0.73  thf('81', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ X0))
% 0.52/0.73           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.52/0.73  thf('82', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('83', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ k1_xboole_0 @ sk_A))),
% 0.52/0.73      inference('demod', [status(thm)], ['59', '81', '82'])).
% 0.52/0.73  thf('84', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.52/0.73  thf('85', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('86', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 0.52/0.73           = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.73  thf('87', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.73           = (k4_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('sup+', [status(thm)], ['85', '86'])).
% 0.52/0.73  thf('88', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.52/0.73      inference('sup+', [status(thm)], ['84', '87'])).
% 0.52/0.73  thf('89', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.73  thf('90', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.52/0.73      inference('demod', [status(thm)], ['88', '89'])).
% 0.52/0.73  thf('91', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.52/0.73           = (k3_xboole_0 @ X15 @ X16))),
% 0.52/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.73  thf('92', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.52/0.73      inference('sup+', [status(thm)], ['90', '91'])).
% 0.52/0.73  thf('93', plain,
% 0.52/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['16', '17'])).
% 0.52/0.73  thf('94', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('95', plain,
% 0.52/0.73      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['93', '94'])).
% 0.52/0.73  thf('96', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('97', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.52/0.73  thf('98', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['92', '95', '96', '97'])).
% 0.52/0.73  thf('99', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['83', '98'])).
% 0.52/0.73  thf('100', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.73  thf('101', plain, (((sk_C) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.52/0.73      inference('demod', [status(thm)], ['58', '99', '100'])).
% 0.52/0.73  thf('102', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['83', '98'])).
% 0.52/0.73  thf('103', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.52/0.73           = (k3_xboole_0 @ X15 @ X16))),
% 0.52/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.73  thf('104', plain,
% 0.52/0.73      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.52/0.73      inference('sup+', [status(thm)], ['102', '103'])).
% 0.52/0.73  thf('105', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.73  thf('106', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.52/0.73      inference('demod', [status(thm)], ['104', '105'])).
% 0.52/0.73  thf('107', plain, (((sk_B) = (sk_C))),
% 0.52/0.73      inference('sup+', [status(thm)], ['101', '106'])).
% 0.52/0.73  thf('108', plain, (((sk_C) != (sk_B))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('109', plain, ($false),
% 0.52/0.73      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 0.52/0.73  
% 0.52/0.73  % SZS output end Refutation
% 0.52/0.73  
% 0.52/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
