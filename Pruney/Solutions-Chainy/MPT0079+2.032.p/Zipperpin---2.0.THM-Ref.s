%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rCW4g8awhu

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:01 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 380 expanded)
%              Number of leaves         :   19 ( 132 expanded)
%              Depth                    :   20
%              Number of atoms          :  673 (3133 expanded)
%              Number of equality atoms :   84 ( 382 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('3',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('5',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['13','26'])).

thf('28',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_A ),
    inference('sup+',[status(thm)],['7','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('42',plain,
    ( ( k2_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('49',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('51',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('54',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['13','26'])).

thf('59',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_D ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['54','61'])).

thf('63',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['46','62'])).

thf('64',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['2','63'])).

thf(t71_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf('65',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ X26 @ X27 )
      | ( ( k2_xboole_0 @ X26 @ X27 )
       != ( k2_xboole_0 @ X28 @ X27 ) )
      | ~ ( r1_xboole_0 @ X28 @ X27 )
      | ( X26 = X28 ) ) ),
    inference(cnf,[status(esa)],[t71_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ X0 @ sk_A )
       != ( k2_xboole_0 @ sk_B @ sk_A ) )
      | ( X0 = sk_C )
      | ~ ( r1_xboole_0 @ sk_C @ sk_A )
      | ~ ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ X0 @ sk_A )
       != ( k2_xboole_0 @ sk_B @ sk_A ) )
      | ( X0 = sk_C )
      | ~ ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_A )
    | ( sk_B = sk_C ) ),
    inference(eq_res,[status(thm)],['68'])).

thf('70',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('72',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['46','62'])).

thf('74',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    sk_B = sk_C ),
    inference(demod,[status(thm)],['69','74'])).

thf('76',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rCW4g8awhu
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.92  % Solved by: fo/fo7.sh
% 0.67/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.92  % done 1107 iterations in 0.462s
% 0.67/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.92  % SZS output start Refutation
% 0.67/0.92  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.92  thf(sk_D_type, type, sk_D: $i).
% 0.67/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.92  thf(t72_xboole_1, conjecture,
% 0.67/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.92     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.67/0.92         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.67/0.92       ( ( C ) = ( B ) ) ))).
% 0.67/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.92    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.92        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.67/0.92            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.67/0.92          ( ( C ) = ( B ) ) ) )),
% 0.67/0.92    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.67/0.92  thf('0', plain,
% 0.67/0.92      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf(commutativity_k2_xboole_0, axiom,
% 0.67/0.92    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.67/0.92  thf('1', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.67/0.92  thf('2', plain,
% 0.67/0.92      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.67/0.92      inference('demod', [status(thm)], ['0', '1'])).
% 0.67/0.92  thf('3', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf(symmetry_r1_xboole_0, axiom,
% 0.67/0.92    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.67/0.92  thf('4', plain,
% 0.67/0.92      (![X5 : $i, X6 : $i]:
% 0.67/0.92         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.67/0.92      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.67/0.92  thf('5', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.67/0.92      inference('sup-', [status(thm)], ['3', '4'])).
% 0.67/0.92  thf(d7_xboole_0, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.67/0.92       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.67/0.92  thf('6', plain,
% 0.67/0.92      (![X2 : $i, X3 : $i]:
% 0.67/0.92         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.67/0.92      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.67/0.92  thf('7', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.67/0.92      inference('sup-', [status(thm)], ['5', '6'])).
% 0.67/0.92  thf(t48_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.67/0.92  thf('8', plain,
% 0.67/0.92      (![X17 : $i, X18 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.67/0.92           = (k3_xboole_0 @ X17 @ X18))),
% 0.67/0.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.67/0.92  thf(t39_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.67/0.92  thf('9', plain,
% 0.67/0.92      (![X10 : $i, X11 : $i]:
% 0.67/0.92         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.67/0.92           = (k2_xboole_0 @ X10 @ X11))),
% 0.67/0.92      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.67/0.92  thf('10', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.67/0.92           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.67/0.92      inference('sup+', [status(thm)], ['8', '9'])).
% 0.67/0.92  thf('11', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.67/0.92  thf('12', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.67/0.92  thf('13', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.67/0.92           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.92      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.67/0.92  thf('14', plain,
% 0.67/0.92      (![X10 : $i, X11 : $i]:
% 0.67/0.92         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.67/0.92           = (k2_xboole_0 @ X10 @ X11))),
% 0.67/0.92      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.67/0.92  thf(t41_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i,C:$i]:
% 0.67/0.92     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.67/0.92       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.67/0.92  thf('15', plain,
% 0.67/0.92      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.67/0.92           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.67/0.92  thf('16', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 0.67/0.92           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['14', '15'])).
% 0.67/0.92  thf('17', plain,
% 0.67/0.92      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.67/0.92           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.67/0.92  thf('18', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 0.67/0.92           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.67/0.92      inference('demod', [status(thm)], ['16', '17'])).
% 0.67/0.92  thf(t1_boole, axiom,
% 0.67/0.92    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.67/0.92  thf('19', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.67/0.92      inference('cnf', [status(esa)], [t1_boole])).
% 0.67/0.92  thf(t46_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.67/0.92  thf('20', plain,
% 0.67/0.92      (![X15 : $i, X16 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 0.67/0.92      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.67/0.92  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['19', '20'])).
% 0.67/0.92  thf('22', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['18', '21'])).
% 0.67/0.92  thf('23', plain,
% 0.67/0.92      (![X10 : $i, X11 : $i]:
% 0.67/0.92         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.67/0.92           = (k2_xboole_0 @ X10 @ X11))),
% 0.67/0.92      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.67/0.92  thf('24', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.67/0.92           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['22', '23'])).
% 0.67/0.92  thf('25', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.67/0.92      inference('cnf', [status(esa)], [t1_boole])).
% 0.67/0.92  thf('26', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.92      inference('demod', [status(thm)], ['24', '25'])).
% 0.67/0.92  thf('27', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.67/0.92           = (X1))),
% 0.67/0.92      inference('demod', [status(thm)], ['13', '26'])).
% 0.67/0.92  thf('28', plain,
% 0.67/0.92      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_A))),
% 0.67/0.92      inference('sup+', [status(thm)], ['7', '27'])).
% 0.67/0.92  thf('29', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.67/0.92  thf('30', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.67/0.92      inference('cnf', [status(esa)], [t1_boole])).
% 0.67/0.92  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['29', '30'])).
% 0.67/0.92  thf('32', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.67/0.92      inference('demod', [status(thm)], ['28', '31'])).
% 0.67/0.92  thf('33', plain,
% 0.67/0.92      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.67/0.92      inference('demod', [status(thm)], ['0', '1'])).
% 0.67/0.92  thf('34', plain,
% 0.67/0.92      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.67/0.92           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.67/0.92  thf('35', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 0.67/0.92           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['33', '34'])).
% 0.67/0.92  thf('36', plain,
% 0.67/0.92      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.67/0.92           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.67/0.92  thf('37', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 0.67/0.92           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.67/0.92      inference('demod', [status(thm)], ['35', '36'])).
% 0.67/0.92  thf('38', plain,
% 0.67/0.92      (((k4_xboole_0 @ sk_A @ sk_D)
% 0.67/0.92         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.67/0.92      inference('sup+', [status(thm)], ['32', '37'])).
% 0.67/0.92  thf('39', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['18', '21'])).
% 0.67/0.92  thf('40', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 0.67/0.92      inference('demod', [status(thm)], ['38', '39'])).
% 0.67/0.92  thf('41', plain,
% 0.67/0.92      (![X10 : $i, X11 : $i]:
% 0.67/0.92         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.67/0.92           = (k2_xboole_0 @ X10 @ X11))),
% 0.67/0.92      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.67/0.92  thf('42', plain,
% 0.67/0.92      (((k2_xboole_0 @ sk_D @ k1_xboole_0) = (k2_xboole_0 @ sk_D @ sk_A))),
% 0.67/0.92      inference('sup+', [status(thm)], ['40', '41'])).
% 0.67/0.92  thf('43', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.67/0.92  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['29', '30'])).
% 0.67/0.92  thf('45', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.67/0.92  thf('46', plain, (((sk_D) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.67/0.92      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.67/0.92  thf('47', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['18', '21'])).
% 0.67/0.92  thf('48', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 0.67/0.92           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.67/0.92      inference('demod', [status(thm)], ['35', '36'])).
% 0.67/0.92  thf('49', plain,
% 0.67/0.92      (((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A))),
% 0.67/0.92      inference('sup+', [status(thm)], ['47', '48'])).
% 0.67/0.92  thf('50', plain,
% 0.67/0.92      (![X10 : $i, X11 : $i]:
% 0.67/0.92         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.67/0.92           = (k2_xboole_0 @ X10 @ X11))),
% 0.67/0.92      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.67/0.92  thf('51', plain,
% 0.67/0.92      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 0.67/0.92         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['49', '50'])).
% 0.67/0.92  thf('52', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.67/0.92  thf('53', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['29', '30'])).
% 0.67/0.92  thf('54', plain,
% 0.67/0.92      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)))),
% 0.67/0.92      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.67/0.92  thf('55', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('56', plain,
% 0.67/0.92      (![X2 : $i, X3 : $i]:
% 0.67/0.92         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.67/0.92      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.67/0.92  thf('57', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.67/0.92      inference('sup-', [status(thm)], ['55', '56'])).
% 0.67/0.92  thf('58', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.67/0.92           = (X1))),
% 0.67/0.92      inference('demod', [status(thm)], ['13', '26'])).
% 0.67/0.92  thf('59', plain,
% 0.67/0.92      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_D))),
% 0.67/0.92      inference('sup+', [status(thm)], ['57', '58'])).
% 0.67/0.92  thf('60', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['29', '30'])).
% 0.67/0.92  thf('61', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 0.67/0.92      inference('demod', [status(thm)], ['59', '60'])).
% 0.67/0.92  thf('62', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.67/0.92      inference('demod', [status(thm)], ['54', '61'])).
% 0.67/0.92  thf('63', plain, (((sk_A) = (sk_D))),
% 0.67/0.92      inference('sup+', [status(thm)], ['46', '62'])).
% 0.67/0.92  thf('64', plain,
% 0.67/0.92      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_A))),
% 0.67/0.92      inference('demod', [status(thm)], ['2', '63'])).
% 0.67/0.92  thf(t71_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i,C:$i]:
% 0.67/0.92     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.67/0.92         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.67/0.92       ( ( A ) = ( C ) ) ))).
% 0.67/0.92  thf('65', plain,
% 0.67/0.92      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.67/0.92         (~ (r1_xboole_0 @ X26 @ X27)
% 0.67/0.92          | ((k2_xboole_0 @ X26 @ X27) != (k2_xboole_0 @ X28 @ X27))
% 0.67/0.92          | ~ (r1_xboole_0 @ X28 @ X27)
% 0.67/0.92          | ((X26) = (X28)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t71_xboole_1])).
% 0.67/0.92  thf('66', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (((k2_xboole_0 @ X0 @ sk_A) != (k2_xboole_0 @ sk_B @ sk_A))
% 0.67/0.92          | ((X0) = (sk_C))
% 0.67/0.92          | ~ (r1_xboole_0 @ sk_C @ sk_A)
% 0.67/0.92          | ~ (r1_xboole_0 @ X0 @ sk_A))),
% 0.67/0.92      inference('sup-', [status(thm)], ['64', '65'])).
% 0.67/0.92  thf('67', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('68', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (((k2_xboole_0 @ X0 @ sk_A) != (k2_xboole_0 @ sk_B @ sk_A))
% 0.67/0.92          | ((X0) = (sk_C))
% 0.67/0.92          | ~ (r1_xboole_0 @ X0 @ sk_A))),
% 0.67/0.92      inference('demod', [status(thm)], ['66', '67'])).
% 0.67/0.92  thf('69', plain, ((~ (r1_xboole_0 @ sk_B @ sk_A) | ((sk_B) = (sk_C)))),
% 0.67/0.92      inference('eq_res', [status(thm)], ['68'])).
% 0.67/0.92  thf('70', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('71', plain,
% 0.67/0.92      (![X5 : $i, X6 : $i]:
% 0.67/0.92         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.67/0.92      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.67/0.92  thf('72', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.67/0.92      inference('sup-', [status(thm)], ['70', '71'])).
% 0.67/0.92  thf('73', plain, (((sk_A) = (sk_D))),
% 0.67/0.92      inference('sup+', [status(thm)], ['46', '62'])).
% 0.67/0.92  thf('74', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.67/0.92      inference('demod', [status(thm)], ['72', '73'])).
% 0.67/0.92  thf('75', plain, (((sk_B) = (sk_C))),
% 0.67/0.92      inference('demod', [status(thm)], ['69', '74'])).
% 0.67/0.92  thf('76', plain, (((sk_C) != (sk_B))),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('77', plain, ($false),
% 0.67/0.92      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.67/0.92  
% 0.67/0.92  % SZS output end Refutation
% 0.67/0.92  
% 0.67/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
