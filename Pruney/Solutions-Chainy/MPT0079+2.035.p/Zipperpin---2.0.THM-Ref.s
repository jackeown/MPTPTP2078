%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WITsDd4AME

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:01 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 658 expanded)
%              Number of leaves         :   22 ( 229 expanded)
%              Depth                    :   16
%              Number of atoms          :  751 (4961 expanded)
%              Number of equality atoms :   99 ( 660 expanded)
%              Maximal formula depth    :   11 (   6 average)

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

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = sk_B ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('13',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_A ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k2_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('42',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X17 ) @ X16 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('49',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','50'])).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,
    ( ( k2_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('57',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('60',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('63',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('65',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_D ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['60','67'])).

thf('69',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('70',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('73',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['57','73'])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['10','74'])).

thf('76',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('78',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['57','73'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('81',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['57','73'])).

thf('82',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('84',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('86',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = sk_C ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('88',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['78','79','80','81','88'])).

thf('90',plain,(
    sk_B = sk_C ),
    inference('sup+',[status(thm)],['75','89'])).

thf('91',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['90','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WITsDd4AME
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:30:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 1.98/2.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.98/2.23  % Solved by: fo/fo7.sh
% 1.98/2.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.98/2.23  % done 684 iterations in 1.759s
% 1.98/2.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.98/2.23  % SZS output start Refutation
% 1.98/2.23  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.98/2.23  thf(sk_D_type, type, sk_D: $i).
% 1.98/2.23  thf(sk_C_type, type, sk_C: $i).
% 1.98/2.23  thf(sk_B_type, type, sk_B: $i).
% 1.98/2.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.98/2.23  thf(sk_A_type, type, sk_A: $i).
% 1.98/2.23  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.98/2.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.98/2.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.98/2.23  thf(t72_xboole_1, conjecture,
% 1.98/2.23    (![A:$i,B:$i,C:$i,D:$i]:
% 1.98/2.23     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.98/2.23         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.98/2.23       ( ( C ) = ( B ) ) ))).
% 1.98/2.23  thf(zf_stmt_0, negated_conjecture,
% 1.98/2.23    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.98/2.23        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.98/2.23            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.98/2.23          ( ( C ) = ( B ) ) ) )),
% 1.98/2.23    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 1.98/2.23  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 1.98/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.23  thf(symmetry_r1_xboole_0, axiom,
% 1.98/2.23    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.98/2.23  thf('1', plain,
% 1.98/2.23      (![X5 : $i, X6 : $i]:
% 1.98/2.23         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.98/2.23      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.98/2.23  thf('2', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 1.98/2.23      inference('sup-', [status(thm)], ['0', '1'])).
% 1.98/2.23  thf(d7_xboole_0, axiom,
% 1.98/2.23    (![A:$i,B:$i]:
% 1.98/2.23     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.98/2.23       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.98/2.23  thf('3', plain,
% 1.98/2.23      (![X2 : $i, X3 : $i]:
% 1.98/2.23         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.98/2.23      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.98/2.23  thf('4', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 1.98/2.23      inference('sup-', [status(thm)], ['2', '3'])).
% 1.98/2.23  thf(t51_xboole_1, axiom,
% 1.98/2.23    (![A:$i,B:$i]:
% 1.98/2.23     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.98/2.23       ( A ) ))).
% 1.98/2.23  thf('5', plain,
% 1.98/2.23      (![X23 : $i, X24 : $i]:
% 1.98/2.23         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 1.98/2.23           = (X23))),
% 1.98/2.23      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.98/2.23  thf('6', plain,
% 1.98/2.23      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_D)) = (sk_B))),
% 1.98/2.23      inference('sup+', [status(thm)], ['4', '5'])).
% 1.98/2.23  thf(commutativity_k2_xboole_0, axiom,
% 1.98/2.23    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.98/2.23  thf('7', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.98/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.98/2.23  thf(t1_boole, axiom,
% 1.98/2.23    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.98/2.23  thf('8', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.98/2.23      inference('cnf', [status(esa)], [t1_boole])).
% 1.98/2.23  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.98/2.23      inference('sup+', [status(thm)], ['7', '8'])).
% 1.98/2.23  thf('10', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 1.98/2.23      inference('demod', [status(thm)], ['6', '9'])).
% 1.98/2.23  thf('11', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 1.98/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.23  thf('12', plain,
% 1.98/2.23      (![X5 : $i, X6 : $i]:
% 1.98/2.23         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.98/2.23      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.98/2.23  thf('13', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 1.98/2.23      inference('sup-', [status(thm)], ['11', '12'])).
% 1.98/2.23  thf('14', plain,
% 1.98/2.23      (![X2 : $i, X3 : $i]:
% 1.98/2.23         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.98/2.23      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.98/2.23  thf('15', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 1.98/2.23      inference('sup-', [status(thm)], ['13', '14'])).
% 1.98/2.23  thf('16', plain,
% 1.98/2.23      (![X23 : $i, X24 : $i]:
% 1.98/2.23         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 1.98/2.23           = (X23))),
% 1.98/2.23      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.98/2.23  thf('17', plain,
% 1.98/2.23      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_A))),
% 1.98/2.23      inference('sup+', [status(thm)], ['15', '16'])).
% 1.98/2.23  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.98/2.23      inference('sup+', [status(thm)], ['7', '8'])).
% 1.98/2.23  thf('19', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 1.98/2.23      inference('demod', [status(thm)], ['17', '18'])).
% 1.98/2.23  thf('20', plain,
% 1.98/2.23      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.98/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.23  thf('21', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.98/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.98/2.23  thf('22', plain,
% 1.98/2.23      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.98/2.23      inference('demod', [status(thm)], ['20', '21'])).
% 1.98/2.23  thf(t41_xboole_1, axiom,
% 1.98/2.23    (![A:$i,B:$i,C:$i]:
% 1.98/2.23     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.98/2.23       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.98/2.23  thf('23', plain,
% 1.98/2.23      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.98/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.98/2.23           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.98/2.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.98/2.23  thf('24', plain,
% 1.98/2.23      (![X0 : $i]:
% 1.98/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 1.98/2.23           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.98/2.23      inference('sup+', [status(thm)], ['22', '23'])).
% 1.98/2.23  thf('25', plain,
% 1.98/2.23      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.98/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.98/2.23           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.98/2.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.98/2.23  thf('26', plain,
% 1.98/2.23      (![X0 : $i]:
% 1.98/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 1.98/2.23           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 1.98/2.23      inference('demod', [status(thm)], ['24', '25'])).
% 1.98/2.23  thf('27', plain,
% 1.98/2.23      (((k4_xboole_0 @ sk_A @ sk_D)
% 1.98/2.23         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 1.98/2.23      inference('sup+', [status(thm)], ['19', '26'])).
% 1.98/2.23  thf(t3_boole, axiom,
% 1.98/2.23    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.98/2.23  thf('28', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 1.98/2.23      inference('cnf', [status(esa)], [t3_boole])).
% 1.98/2.23  thf(t48_xboole_1, axiom,
% 1.98/2.23    (![A:$i,B:$i]:
% 1.98/2.23     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.98/2.23  thf('29', plain,
% 1.98/2.23      (![X18 : $i, X19 : $i]:
% 1.98/2.23         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.98/2.23           = (k3_xboole_0 @ X18 @ X19))),
% 1.98/2.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.98/2.23  thf('30', plain,
% 1.98/2.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.98/2.23      inference('sup+', [status(thm)], ['28', '29'])).
% 1.98/2.23  thf(t2_boole, axiom,
% 1.98/2.23    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.98/2.23  thf('31', plain,
% 1.98/2.23      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.98/2.23      inference('cnf', [status(esa)], [t2_boole])).
% 1.98/2.23  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.98/2.23      inference('demod', [status(thm)], ['30', '31'])).
% 1.98/2.23  thf(t39_xboole_1, axiom,
% 1.98/2.23    (![A:$i,B:$i]:
% 1.98/2.23     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.98/2.23  thf('33', plain,
% 1.98/2.23      (![X9 : $i, X10 : $i]:
% 1.98/2.23         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 1.98/2.23           = (k2_xboole_0 @ X9 @ X10))),
% 1.98/2.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.98/2.23  thf('34', plain,
% 1.98/2.23      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 1.98/2.23      inference('sup+', [status(thm)], ['32', '33'])).
% 1.98/2.23  thf('35', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.98/2.23      inference('cnf', [status(esa)], [t1_boole])).
% 1.98/2.23  thf('36', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.98/2.23      inference('demod', [status(thm)], ['34', '35'])).
% 1.98/2.23  thf(t4_xboole_1, axiom,
% 1.98/2.23    (![A:$i,B:$i,C:$i]:
% 1.98/2.23     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.98/2.23       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.98/2.23  thf('37', plain,
% 1.98/2.23      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.98/2.23         ((k2_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X22)
% 1.98/2.23           = (k2_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 1.98/2.23      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.98/2.23  thf('38', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.98/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.98/2.23  thf('39', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.98/2.23         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 1.98/2.23           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.98/2.23      inference('sup+', [status(thm)], ['37', '38'])).
% 1.98/2.23  thf('40', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]:
% 1.98/2.23         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.98/2.23           = (k2_xboole_0 @ X1 @ X0))),
% 1.98/2.23      inference('sup+', [status(thm)], ['36', '39'])).
% 1.98/2.23  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.98/2.23      inference('demod', [status(thm)], ['30', '31'])).
% 1.98/2.23  thf(t42_xboole_1, axiom,
% 1.98/2.23    (![A:$i,B:$i,C:$i]:
% 1.98/2.23     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.98/2.23       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 1.98/2.23  thf('42', plain,
% 1.98/2.23      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.98/2.23         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X17) @ X16)
% 1.98/2.23           = (k2_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ 
% 1.98/2.23              (k4_xboole_0 @ X17 @ X16)))),
% 1.98/2.23      inference('cnf', [status(esa)], [t42_xboole_1])).
% 1.98/2.23  thf('43', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]:
% 1.98/2.23         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.98/2.23           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 1.98/2.23      inference('sup+', [status(thm)], ['41', '42'])).
% 1.98/2.23  thf('44', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.98/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.98/2.23  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.98/2.23      inference('sup+', [status(thm)], ['7', '8'])).
% 1.98/2.23  thf('46', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]:
% 1.98/2.23         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.98/2.23           = (k4_xboole_0 @ X1 @ X0))),
% 1.98/2.23      inference('demod', [status(thm)], ['43', '44', '45'])).
% 1.98/2.23  thf('47', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]:
% 1.98/2.23         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 1.98/2.23           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.98/2.23      inference('sup+', [status(thm)], ['40', '46'])).
% 1.98/2.23  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.98/2.23      inference('demod', [status(thm)], ['30', '31'])).
% 1.98/2.23  thf('49', plain,
% 1.98/2.23      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.98/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.98/2.23           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.98/2.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.98/2.23  thf('50', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]:
% 1.98/2.23         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.98/2.23      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.98/2.23  thf('51', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 1.98/2.23      inference('demod', [status(thm)], ['27', '50'])).
% 1.98/2.23  thf('52', plain,
% 1.98/2.23      (![X9 : $i, X10 : $i]:
% 1.98/2.23         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 1.98/2.23           = (k2_xboole_0 @ X9 @ X10))),
% 1.98/2.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.98/2.23  thf('53', plain,
% 1.98/2.23      (((k2_xboole_0 @ sk_D @ k1_xboole_0) = (k2_xboole_0 @ sk_D @ sk_A))),
% 1.98/2.23      inference('sup+', [status(thm)], ['51', '52'])).
% 1.98/2.23  thf('54', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.98/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.98/2.23  thf('55', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.98/2.23      inference('sup+', [status(thm)], ['7', '8'])).
% 1.98/2.23  thf('56', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.98/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.98/2.23  thf('57', plain, (((sk_D) = (k2_xboole_0 @ sk_A @ sk_D))),
% 1.98/2.23      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 1.98/2.23  thf('58', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]:
% 1.98/2.23         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.98/2.23      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.98/2.23  thf('59', plain,
% 1.98/2.23      (![X0 : $i]:
% 1.98/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 1.98/2.23           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 1.98/2.23      inference('demod', [status(thm)], ['24', '25'])).
% 1.98/2.23  thf('60', plain,
% 1.98/2.23      (((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A))),
% 1.98/2.23      inference('sup+', [status(thm)], ['58', '59'])).
% 1.98/2.23  thf('61', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 1.98/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.23  thf('62', plain,
% 1.98/2.23      (![X2 : $i, X3 : $i]:
% 1.98/2.23         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.98/2.23      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.98/2.23  thf('63', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 1.98/2.23      inference('sup-', [status(thm)], ['61', '62'])).
% 1.98/2.23  thf('64', plain,
% 1.98/2.23      (![X23 : $i, X24 : $i]:
% 1.98/2.23         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 1.98/2.23           = (X23))),
% 1.98/2.23      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.98/2.23  thf('65', plain,
% 1.98/2.23      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_D))),
% 1.98/2.23      inference('sup+', [status(thm)], ['63', '64'])).
% 1.98/2.23  thf('66', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.98/2.23      inference('sup+', [status(thm)], ['7', '8'])).
% 1.98/2.23  thf('67', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 1.98/2.23      inference('demod', [status(thm)], ['65', '66'])).
% 1.98/2.23  thf('68', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 1.98/2.23      inference('demod', [status(thm)], ['60', '67'])).
% 1.98/2.23  thf('69', plain,
% 1.98/2.23      (![X9 : $i, X10 : $i]:
% 1.98/2.23         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 1.98/2.23           = (k2_xboole_0 @ X9 @ X10))),
% 1.98/2.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.98/2.23  thf('70', plain,
% 1.98/2.23      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_D))),
% 1.98/2.23      inference('sup+', [status(thm)], ['68', '69'])).
% 1.98/2.23  thf('71', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.98/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.98/2.23  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.98/2.23      inference('sup+', [status(thm)], ['7', '8'])).
% 1.98/2.23  thf('73', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 1.98/2.23      inference('demod', [status(thm)], ['70', '71', '72'])).
% 1.98/2.23  thf('74', plain, (((sk_A) = (sk_D))),
% 1.98/2.23      inference('sup+', [status(thm)], ['57', '73'])).
% 1.98/2.23  thf('75', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.98/2.23      inference('demod', [status(thm)], ['10', '74'])).
% 1.98/2.23  thf('76', plain,
% 1.98/2.23      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.98/2.23      inference('demod', [status(thm)], ['20', '21'])).
% 1.98/2.23  thf('77', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]:
% 1.98/2.23         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.98/2.23           = (k4_xboole_0 @ X1 @ X0))),
% 1.98/2.23      inference('demod', [status(thm)], ['43', '44', '45'])).
% 1.98/2.23  thf('78', plain,
% 1.98/2.23      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 1.98/2.23         = (k4_xboole_0 @ sk_C @ sk_D))),
% 1.98/2.23      inference('sup+', [status(thm)], ['76', '77'])).
% 1.98/2.23  thf('79', plain, (((sk_A) = (sk_D))),
% 1.98/2.23      inference('sup+', [status(thm)], ['57', '73'])).
% 1.98/2.23  thf('80', plain,
% 1.98/2.23      (![X0 : $i, X1 : $i]:
% 1.98/2.23         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.98/2.23           = (k4_xboole_0 @ X1 @ X0))),
% 1.98/2.23      inference('demod', [status(thm)], ['43', '44', '45'])).
% 1.98/2.23  thf('81', plain, (((sk_A) = (sk_D))),
% 1.98/2.23      inference('sup+', [status(thm)], ['57', '73'])).
% 1.98/2.23  thf('82', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 1.98/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.23  thf('83', plain,
% 1.98/2.23      (![X2 : $i, X3 : $i]:
% 1.98/2.23         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.98/2.23      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.98/2.23  thf('84', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 1.98/2.23      inference('sup-', [status(thm)], ['82', '83'])).
% 1.98/2.23  thf('85', plain,
% 1.98/2.23      (![X23 : $i, X24 : $i]:
% 1.98/2.23         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 1.98/2.23           = (X23))),
% 1.98/2.23      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.98/2.23  thf('86', plain,
% 1.98/2.23      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A)) = (sk_C))),
% 1.98/2.23      inference('sup+', [status(thm)], ['84', '85'])).
% 1.98/2.23  thf('87', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.98/2.23      inference('sup+', [status(thm)], ['7', '8'])).
% 1.98/2.23  thf('88', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 1.98/2.23      inference('demod', [status(thm)], ['86', '87'])).
% 1.98/2.23  thf('89', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 1.98/2.23      inference('demod', [status(thm)], ['78', '79', '80', '81', '88'])).
% 1.98/2.23  thf('90', plain, (((sk_B) = (sk_C))),
% 1.98/2.23      inference('sup+', [status(thm)], ['75', '89'])).
% 1.98/2.23  thf('91', plain, (((sk_C) != (sk_B))),
% 1.98/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.23  thf('92', plain, ($false),
% 1.98/2.23      inference('simplify_reflect-', [status(thm)], ['90', '91'])).
% 1.98/2.23  
% 1.98/2.23  % SZS output end Refutation
% 1.98/2.23  
% 1.98/2.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
