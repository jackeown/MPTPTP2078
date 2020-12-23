%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.klFNZbZ0bz

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:02 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  214 (3755 expanded)
%              Number of leaves         :   20 (1257 expanded)
%              Depth                    :   31
%              Number of atoms          : 1520 (28608 expanded)
%              Number of equality atoms :  190 (3658 expanded)
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

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_C @ sk_D ) )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_D ) @ ( k2_xboole_0 @ sk_B @ sk_A ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_D ) @ sk_B ) @ sk_A )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_D @ k1_xboole_0 ) @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['5','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_D ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_D )
    = ( k3_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('41',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','39','40'])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_xboole_0 @ k1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ k1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_xboole_0 @ k1_xboole_0 @ sk_D ),
    inference(simplify,[status(thm)],['47'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('50',plain,(
    r1_xboole_0 @ sk_D @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_D @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('58',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('62',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = sk_B ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('64',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('68',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('70',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('73',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    r1_xboole_0 @ sk_B @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('79',plain,
    ( ( k3_xboole_0 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('81',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['26','33'])).

thf('82',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['21','52','55','79','80','81'])).

thf('83',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('85',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('87',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('89',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_A ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('91',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('95',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('96',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('98',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('100',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('102',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    r1_xboole_0 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('105',plain,(
    r1_xboole_0 @ sk_A @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('107',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['82','107'])).

thf('109',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('110',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('112',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k2_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('113',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('114',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k2_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['108','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ X0 )
      = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C )
    = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('121',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('122',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k2_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['130','131','134'])).

thf('136',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['119','120','135'])).

thf('137',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('138',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['136','139'])).

thf('141',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('142',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('143',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('144',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('146',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('148',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = sk_C ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('150',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['140','141','142','143','150'])).

thf('152',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['62','63'])).

thf('153',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['140','141','142','143','150'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('155',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('157',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('159',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_C )
    = ( k4_xboole_0 @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['157','160'])).

thf('162',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['140','141','142','143','150'])).

thf('163',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['155','156','161','162'])).

thf('164',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('165',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_D @ sk_C ) @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_D @ sk_C ) ) ),
    inference('sup+',[status(thm)],['165','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('174',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['163','164'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('176',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_C ) )
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['172','173','174','175'])).

thf('177',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['82','107'])).

thf('178',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('179',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('181',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['176','181'])).

thf('183',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['163','164'])).

thf('184',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('185',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_D @ sk_C ) @ sk_A )
    = sk_D ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('187',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['182','187'])).

thf('189',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['152','188'])).

thf('190',plain,(
    sk_C = sk_B ),
    inference('sup+',[status(thm)],['151','189'])).

thf('191',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['190','191'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.klFNZbZ0bz
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.81  % Solved by: fo/fo7.sh
% 0.61/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.81  % done 556 iterations in 0.358s
% 0.61/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.81  % SZS output start Refutation
% 0.61/0.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.61/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.81  thf(sk_D_type, type, sk_D: $i).
% 0.61/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(t72_xboole_1, conjecture,
% 0.61/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.81     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.61/0.81         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.61/0.81       ( ( C ) = ( B ) ) ))).
% 0.61/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.81    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.81        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.61/0.81            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.61/0.81          ( ( C ) = ( B ) ) ) )),
% 0.61/0.81    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.61/0.81  thf('0', plain,
% 0.61/0.81      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(commutativity_k2_xboole_0, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.61/0.81  thf('1', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.81  thf('2', plain,
% 0.61/0.81      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.61/0.81      inference('demod', [status(thm)], ['0', '1'])).
% 0.61/0.81  thf(t3_boole, axiom,
% 0.61/0.81    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.61/0.81  thf('3', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.61/0.81      inference('cnf', [status(esa)], [t3_boole])).
% 0.61/0.81  thf(t48_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.61/0.81  thf('4', plain,
% 0.61/0.81      (![X17 : $i, X18 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.61/0.81           = (k3_xboole_0 @ X17 @ X18))),
% 0.61/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.81  thf('5', plain,
% 0.61/0.81      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['3', '4'])).
% 0.61/0.81  thf('6', plain,
% 0.61/0.81      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.61/0.81      inference('demod', [status(thm)], ['0', '1'])).
% 0.61/0.81  thf(t40_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.61/0.81  thf('7', plain,
% 0.61/0.81      (![X10 : $i, X11 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.61/0.81           = (k4_xboole_0 @ X10 @ X11))),
% 0.61/0.81      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.61/0.81  thf('8', plain,
% 0.61/0.81      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 0.61/0.81         = (k4_xboole_0 @ sk_C @ sk_D))),
% 0.61/0.81      inference('sup+', [status(thm)], ['6', '7'])).
% 0.61/0.81  thf(t39_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.81  thf('9', plain,
% 0.61/0.81      (![X7 : $i, X8 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.61/0.81           = (k2_xboole_0 @ X7 @ X8))),
% 0.61/0.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.81  thf('10', plain,
% 0.61/0.81      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_C @ sk_D))
% 0.61/0.81         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['8', '9'])).
% 0.61/0.81  thf('11', plain,
% 0.61/0.81      (![X7 : $i, X8 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.61/0.81           = (k2_xboole_0 @ X7 @ X8))),
% 0.61/0.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.81  thf('12', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.81  thf('13', plain,
% 0.61/0.81      (((k2_xboole_0 @ sk_C @ sk_D)
% 0.61/0.81         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.61/0.81  thf('14', plain,
% 0.61/0.81      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.61/0.81      inference('demod', [status(thm)], ['0', '1'])).
% 0.61/0.81  thf('15', plain,
% 0.61/0.81      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.61/0.81         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('demod', [status(thm)], ['13', '14'])).
% 0.61/0.81  thf(t41_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.61/0.81       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.61/0.81  thf('16', plain,
% 0.61/0.81      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.61/0.81           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.61/0.81  thf('17', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_D) @ 
% 0.61/0.81           (k2_xboole_0 @ sk_B @ sk_A))
% 0.61/0.81           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['15', '16'])).
% 0.61/0.81  thf('18', plain,
% 0.61/0.81      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.61/0.81           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.61/0.81  thf('19', plain,
% 0.61/0.81      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.61/0.81           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.61/0.81  thf('20', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_D) @ sk_B) @ 
% 0.61/0.81           sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.61/0.81  thf('21', plain,
% 0.61/0.81      (((k4_xboole_0 @ 
% 0.61/0.81         (k4_xboole_0 @ (k3_xboole_0 @ sk_D @ k1_xboole_0) @ sk_B) @ sk_A)
% 0.61/0.81         = (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A))),
% 0.61/0.81      inference('sup+', [status(thm)], ['5', '20'])).
% 0.61/0.81  thf('22', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(d7_xboole_0, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.61/0.81       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.61/0.81  thf('23', plain,
% 0.61/0.81      (![X2 : $i, X3 : $i]:
% 0.61/0.81         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.61/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.61/0.81  thf('24', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['22', '23'])).
% 0.61/0.81  thf(t51_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.61/0.81       ( A ) ))).
% 0.61/0.81  thf('25', plain,
% 0.61/0.81      (![X22 : $i, X23 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 0.61/0.81           = (X22))),
% 0.61/0.81      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.61/0.81  thf('26', plain,
% 0.61/0.81      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_D))),
% 0.61/0.81      inference('sup+', [status(thm)], ['24', '25'])).
% 0.61/0.81  thf('27', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.61/0.81      inference('cnf', [status(esa)], [t3_boole])).
% 0.61/0.81  thf('28', plain,
% 0.61/0.81      (![X10 : $i, X11 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.61/0.81           = (k4_xboole_0 @ X10 @ X11))),
% 0.61/0.81      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.61/0.81  thf('29', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['27', '28'])).
% 0.61/0.81  thf('30', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.61/0.81      inference('cnf', [status(esa)], [t3_boole])).
% 0.61/0.81  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.61/0.81      inference('demod', [status(thm)], ['29', '30'])).
% 0.61/0.81  thf('32', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.81  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['31', '32'])).
% 0.61/0.81  thf('34', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 0.61/0.81      inference('demod', [status(thm)], ['26', '33'])).
% 0.61/0.81  thf('35', plain,
% 0.61/0.81      (![X17 : $i, X18 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.61/0.81           = (k3_xboole_0 @ X17 @ X18))),
% 0.61/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.81  thf('36', plain,
% 0.61/0.81      (((k4_xboole_0 @ sk_D @ sk_D) = (k3_xboole_0 @ sk_D @ sk_B))),
% 0.61/0.81      inference('sup+', [status(thm)], ['34', '35'])).
% 0.61/0.81  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['31', '32'])).
% 0.61/0.81  thf('38', plain,
% 0.61/0.81      (![X10 : $i, X11 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.61/0.81           = (k4_xboole_0 @ X10 @ X11))),
% 0.61/0.81      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.61/0.81  thf('39', plain,
% 0.61/0.81      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['37', '38'])).
% 0.61/0.81  thf('40', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['22', '23'])).
% 0.61/0.81  thf('41', plain, (((k4_xboole_0 @ k1_xboole_0 @ sk_D) = (k1_xboole_0))),
% 0.61/0.81      inference('demod', [status(thm)], ['36', '39', '40'])).
% 0.61/0.81  thf('42', plain,
% 0.61/0.81      (![X17 : $i, X18 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.61/0.81           = (k3_xboole_0 @ X17 @ X18))),
% 0.61/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.81  thf('43', plain,
% 0.61/0.81      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.61/0.81         = (k3_xboole_0 @ k1_xboole_0 @ sk_D))),
% 0.61/0.81      inference('sup+', [status(thm)], ['41', '42'])).
% 0.61/0.81  thf('44', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.61/0.81      inference('cnf', [status(esa)], [t3_boole])).
% 0.61/0.81  thf('45', plain, (((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_D))),
% 0.61/0.81      inference('demod', [status(thm)], ['43', '44'])).
% 0.61/0.81  thf('46', plain,
% 0.61/0.81      (![X2 : $i, X4 : $i]:
% 0.61/0.81         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.61/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.61/0.81  thf('47', plain,
% 0.61/0.81      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ sk_D))),
% 0.61/0.81      inference('sup-', [status(thm)], ['45', '46'])).
% 0.61/0.81  thf('48', plain, ((r1_xboole_0 @ k1_xboole_0 @ sk_D)),
% 0.61/0.81      inference('simplify', [status(thm)], ['47'])).
% 0.61/0.81  thf(symmetry_r1_xboole_0, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.61/0.81  thf('49', plain,
% 0.61/0.81      (![X5 : $i, X6 : $i]:
% 0.61/0.81         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.61/0.81      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.61/0.81  thf('50', plain, ((r1_xboole_0 @ sk_D @ k1_xboole_0)),
% 0.61/0.81      inference('sup-', [status(thm)], ['48', '49'])).
% 0.61/0.81  thf('51', plain,
% 0.61/0.81      (![X2 : $i, X3 : $i]:
% 0.61/0.81         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.61/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.61/0.81  thf('52', plain, (((k3_xboole_0 @ sk_D @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['50', '51'])).
% 0.61/0.81  thf('53', plain,
% 0.61/0.81      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['3', '4'])).
% 0.61/0.81  thf('54', plain,
% 0.61/0.81      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['37', '38'])).
% 0.61/0.81  thf('55', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['53', '54'])).
% 0.61/0.81  thf('56', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('57', plain,
% 0.61/0.81      (![X5 : $i, X6 : $i]:
% 0.61/0.81         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.61/0.81      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.61/0.81  thf('58', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.61/0.81      inference('sup-', [status(thm)], ['56', '57'])).
% 0.61/0.81  thf('59', plain,
% 0.61/0.81      (![X2 : $i, X3 : $i]:
% 0.61/0.81         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.61/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.61/0.81  thf('60', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['58', '59'])).
% 0.61/0.81  thf('61', plain,
% 0.61/0.81      (![X22 : $i, X23 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 0.61/0.81           = (X22))),
% 0.61/0.81      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.61/0.81  thf('62', plain,
% 0.61/0.81      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_D)) = (sk_B))),
% 0.61/0.81      inference('sup+', [status(thm)], ['60', '61'])).
% 0.61/0.81  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['31', '32'])).
% 0.61/0.81  thf('64', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 0.61/0.81      inference('demod', [status(thm)], ['62', '63'])).
% 0.61/0.81  thf('65', plain,
% 0.61/0.81      (![X17 : $i, X18 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.61/0.81           = (k3_xboole_0 @ X17 @ X18))),
% 0.61/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.81  thf('66', plain,
% 0.61/0.81      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_D))),
% 0.61/0.81      inference('sup+', [status(thm)], ['64', '65'])).
% 0.61/0.81  thf('67', plain,
% 0.61/0.81      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['37', '38'])).
% 0.61/0.81  thf('68', plain,
% 0.61/0.81      (((k4_xboole_0 @ k1_xboole_0 @ sk_B) = (k3_xboole_0 @ sk_B @ sk_D))),
% 0.61/0.81      inference('demod', [status(thm)], ['66', '67'])).
% 0.61/0.81  thf('69', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['58', '59'])).
% 0.61/0.81  thf('70', plain, (((k4_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['68', '69'])).
% 0.61/0.81  thf('71', plain,
% 0.61/0.81      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['37', '38'])).
% 0.61/0.81  thf('72', plain,
% 0.61/0.81      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['3', '4'])).
% 0.61/0.81  thf('73', plain,
% 0.61/0.81      (![X2 : $i, X4 : $i]:
% 0.61/0.81         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.61/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.61/0.81  thf('74', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (((k4_xboole_0 @ X0 @ X0) != (k1_xboole_0))
% 0.61/0.81          | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['72', '73'])).
% 0.61/0.81  thf('75', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.61/0.81          | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['71', '74'])).
% 0.61/0.81  thf('76', plain,
% 0.61/0.81      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['70', '75'])).
% 0.61/0.81  thf('77', plain, ((r1_xboole_0 @ sk_B @ k1_xboole_0)),
% 0.61/0.81      inference('simplify', [status(thm)], ['76'])).
% 0.61/0.81  thf('78', plain,
% 0.61/0.81      (![X2 : $i, X3 : $i]:
% 0.61/0.81         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.61/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.61/0.81  thf('79', plain, (((k3_xboole_0 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['77', '78'])).
% 0.61/0.81  thf('80', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['53', '54'])).
% 0.61/0.81  thf('81', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 0.61/0.81      inference('demod', [status(thm)], ['26', '33'])).
% 0.61/0.81  thf('82', plain,
% 0.61/0.81      (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['21', '52', '55', '79', '80', '81'])).
% 0.61/0.81  thf('83', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('84', plain,
% 0.61/0.81      (![X5 : $i, X6 : $i]:
% 0.61/0.81         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.61/0.81      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.61/0.81  thf('85', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.61/0.81      inference('sup-', [status(thm)], ['83', '84'])).
% 0.61/0.81  thf('86', plain,
% 0.61/0.81      (![X2 : $i, X3 : $i]:
% 0.61/0.81         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.61/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.61/0.81  thf('87', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['85', '86'])).
% 0.61/0.81  thf('88', plain,
% 0.61/0.81      (![X22 : $i, X23 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 0.61/0.81           = (X22))),
% 0.61/0.81      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.61/0.81  thf('89', plain,
% 0.61/0.81      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_A))),
% 0.61/0.81      inference('sup+', [status(thm)], ['87', '88'])).
% 0.61/0.81  thf('90', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['31', '32'])).
% 0.61/0.81  thf('91', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['89', '90'])).
% 0.61/0.81  thf('92', plain,
% 0.61/0.81      (![X17 : $i, X18 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.61/0.81           = (k3_xboole_0 @ X17 @ X18))),
% 0.61/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.81  thf('93', plain,
% 0.61/0.81      (((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.61/0.81      inference('sup+', [status(thm)], ['91', '92'])).
% 0.61/0.81  thf('94', plain,
% 0.61/0.81      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['37', '38'])).
% 0.61/0.81  thf('95', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['85', '86'])).
% 0.61/0.81  thf('96', plain, (((k4_xboole_0 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.61/0.81      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.61/0.81  thf('97', plain,
% 0.61/0.81      (![X17 : $i, X18 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.61/0.81           = (k3_xboole_0 @ X17 @ X18))),
% 0.61/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.81  thf('98', plain,
% 0.61/0.81      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.61/0.81         = (k3_xboole_0 @ k1_xboole_0 @ sk_A))),
% 0.61/0.81      inference('sup+', [status(thm)], ['96', '97'])).
% 0.61/0.81  thf('99', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.61/0.81      inference('cnf', [status(esa)], [t3_boole])).
% 0.61/0.81  thf('100', plain, (((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['98', '99'])).
% 0.61/0.81  thf('101', plain,
% 0.61/0.81      (![X2 : $i, X4 : $i]:
% 0.61/0.81         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.61/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.61/0.81  thf('102', plain,
% 0.61/0.81      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ sk_A))),
% 0.61/0.81      inference('sup-', [status(thm)], ['100', '101'])).
% 0.61/0.81  thf('103', plain, ((r1_xboole_0 @ k1_xboole_0 @ sk_A)),
% 0.61/0.81      inference('simplify', [status(thm)], ['102'])).
% 0.61/0.81  thf('104', plain,
% 0.61/0.81      (![X5 : $i, X6 : $i]:
% 0.61/0.81         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.61/0.81      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.61/0.81  thf('105', plain, ((r1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.61/0.81      inference('sup-', [status(thm)], ['103', '104'])).
% 0.61/0.81  thf('106', plain,
% 0.61/0.81      (![X2 : $i, X3 : $i]:
% 0.61/0.81         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.61/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.61/0.81  thf('107', plain, (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['105', '106'])).
% 0.61/0.81  thf('108', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['82', '107'])).
% 0.61/0.81  thf('109', plain,
% 0.61/0.81      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.61/0.81           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.61/0.81  thf('110', plain,
% 0.61/0.81      (![X7 : $i, X8 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.61/0.81           = (k2_xboole_0 @ X7 @ X8))),
% 0.61/0.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.81  thf('111', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.61/0.81           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.61/0.81           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.61/0.81      inference('sup+', [status(thm)], ['109', '110'])).
% 0.61/0.81  thf(t4_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.61/0.81       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.61/0.81  thf('112', plain,
% 0.61/0.81      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X21)
% 0.61/0.81           = (k2_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.61/0.81  thf('113', plain,
% 0.61/0.81      (![X7 : $i, X8 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.61/0.81           = (k2_xboole_0 @ X7 @ X8))),
% 0.61/0.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.81  thf('114', plain,
% 0.61/0.81      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X21)
% 0.61/0.81           = (k2_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.61/0.81  thf('115', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))
% 0.61/0.81           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 0.61/0.81      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 0.61/0.81  thf('116', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.61/0.81           = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_D)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['108', '115'])).
% 0.61/0.81  thf('117', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.61/0.81      inference('demod', [status(thm)], ['29', '30'])).
% 0.61/0.81  thf('118', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ sk_A @ X0)
% 0.61/0.81           = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_D)))),
% 0.61/0.81      inference('demod', [status(thm)], ['116', '117'])).
% 0.61/0.81  thf('119', plain,
% 0.61/0.81      (((k2_xboole_0 @ sk_A @ sk_C)
% 0.61/0.81         = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['2', '118'])).
% 0.61/0.81  thf('120', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.81  thf('121', plain,
% 0.61/0.81      (![X10 : $i, X11 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.61/0.81           = (k4_xboole_0 @ X10 @ X11))),
% 0.61/0.81      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.61/0.81  thf('122', plain,
% 0.61/0.81      (![X7 : $i, X8 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.61/0.81           = (k2_xboole_0 @ X7 @ X8))),
% 0.61/0.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.81  thf('123', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.61/0.81           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['121', '122'])).
% 0.61/0.81  thf('124', plain,
% 0.61/0.81      (![X7 : $i, X8 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.61/0.81           = (k2_xboole_0 @ X7 @ X8))),
% 0.61/0.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.81  thf('125', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X0 @ X1)
% 0.61/0.81           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['123', '124'])).
% 0.61/0.81  thf('126', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X0 @ X1)
% 0.61/0.81           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['123', '124'])).
% 0.61/0.81  thf('127', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1)
% 0.61/0.81           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['125', '126'])).
% 0.61/0.81  thf('128', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.81  thf('129', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X0 @ X1)
% 0.61/0.81           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['123', '124'])).
% 0.61/0.81  thf('130', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X1 @ X0)
% 0.61/0.81           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.61/0.81  thf('131', plain,
% 0.61/0.81      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X21)
% 0.61/0.81           = (k2_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.61/0.81  thf('132', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.81  thf('133', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X0 @ X1)
% 0.61/0.81           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['123', '124'])).
% 0.61/0.81  thf('134', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X1 @ X0)
% 0.61/0.81           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['132', '133'])).
% 0.61/0.81  thf('135', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X1 @ X0)
% 0.61/0.81           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['130', '131', '134'])).
% 0.61/0.81  thf('136', plain,
% 0.61/0.81      (((k2_xboole_0 @ sk_C @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['119', '120', '135'])).
% 0.61/0.81  thf('137', plain,
% 0.61/0.81      (![X7 : $i, X8 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.61/0.81           = (k2_xboole_0 @ X7 @ X8))),
% 0.61/0.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.81  thf('138', plain,
% 0.61/0.81      (![X10 : $i, X11 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.61/0.81           = (k4_xboole_0 @ X10 @ X11))),
% 0.61/0.81      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.61/0.81  thf('139', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.61/0.81           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['137', '138'])).
% 0.61/0.81  thf('140', plain,
% 0.61/0.81      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 0.61/0.81         (k4_xboole_0 @ sk_A @ sk_C))
% 0.61/0.81         = (k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['136', '139'])).
% 0.61/0.81  thf('141', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['89', '90'])).
% 0.61/0.81  thf('142', plain,
% 0.61/0.81      (![X10 : $i, X11 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.61/0.81           = (k4_xboole_0 @ X10 @ X11))),
% 0.61/0.81      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.61/0.81  thf('143', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['89', '90'])).
% 0.61/0.81  thf('144', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('145', plain,
% 0.61/0.81      (![X2 : $i, X3 : $i]:
% 0.61/0.81         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.61/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.61/0.81  thf('146', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['144', '145'])).
% 0.61/0.81  thf('147', plain,
% 0.61/0.81      (![X22 : $i, X23 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 0.61/0.81           = (X22))),
% 0.61/0.81      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.61/0.81  thf('148', plain,
% 0.61/0.81      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A)) = (sk_C))),
% 0.61/0.81      inference('sup+', [status(thm)], ['146', '147'])).
% 0.61/0.81  thf('149', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['31', '32'])).
% 0.61/0.81  thf('150', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.61/0.81      inference('demod', [status(thm)], ['148', '149'])).
% 0.61/0.81  thf('151', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 0.61/0.81      inference('demod', [status(thm)], ['140', '141', '142', '143', '150'])).
% 0.61/0.81  thf('152', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 0.61/0.81      inference('demod', [status(thm)], ['62', '63'])).
% 0.61/0.81  thf('153', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 0.61/0.81      inference('demod', [status(thm)], ['140', '141', '142', '143', '150'])).
% 0.61/0.81  thf('154', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.61/0.81           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['137', '138'])).
% 0.61/0.81  thf('155', plain,
% 0.61/0.81      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.61/0.81         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['153', '154'])).
% 0.61/0.81  thf('156', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.81  thf('157', plain,
% 0.61/0.81      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.61/0.81      inference('demod', [status(thm)], ['0', '1'])).
% 0.61/0.81  thf('158', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.81  thf('159', plain,
% 0.61/0.81      (![X10 : $i, X11 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.61/0.81           = (k4_xboole_0 @ X10 @ X11))),
% 0.61/0.81      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.61/0.81  thf('160', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.61/0.81           = (k4_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['158', '159'])).
% 0.61/0.81  thf('161', plain,
% 0.61/0.81      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_C)
% 0.61/0.82         = (k4_xboole_0 @ sk_D @ sk_C))),
% 0.61/0.82      inference('sup+', [status(thm)], ['157', '160'])).
% 0.61/0.82  thf('162', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['140', '141', '142', '143', '150'])).
% 0.61/0.82  thf('163', plain,
% 0.61/0.82      (((k4_xboole_0 @ sk_D @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['155', '156', '161', '162'])).
% 0.61/0.82  thf('164', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.61/0.82      inference('demod', [status(thm)], ['89', '90'])).
% 0.61/0.82  thf('165', plain, (((k4_xboole_0 @ sk_D @ sk_C) = (sk_A))),
% 0.61/0.82      inference('demod', [status(thm)], ['163', '164'])).
% 0.61/0.82  thf('166', plain,
% 0.61/0.82      (![X22 : $i, X23 : $i]:
% 0.61/0.82         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 0.61/0.82           = (X22))),
% 0.61/0.82      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.61/0.82  thf('167', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k2_xboole_0 @ X0 @ X1)
% 0.61/0.82           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.82      inference('demod', [status(thm)], ['123', '124'])).
% 0.61/0.82  thf('168', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 0.61/0.82           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.61/0.82      inference('sup+', [status(thm)], ['166', '167'])).
% 0.61/0.82  thf('169', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.82  thf('170', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.82  thf('171', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 0.61/0.82           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.61/0.82      inference('demod', [status(thm)], ['168', '169', '170'])).
% 0.61/0.82  thf('172', plain,
% 0.61/0.82      (((k2_xboole_0 @ (k3_xboole_0 @ sk_D @ sk_C) @ sk_A)
% 0.61/0.82         = (k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_D @ sk_C)))),
% 0.61/0.82      inference('sup+', [status(thm)], ['165', '171'])).
% 0.61/0.82  thf('173', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.82  thf('174', plain, (((k4_xboole_0 @ sk_D @ sk_C) = (sk_A))),
% 0.61/0.82      inference('demod', [status(thm)], ['163', '164'])).
% 0.61/0.82  thf('175', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.82  thf('176', plain,
% 0.61/0.82      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_C))
% 0.61/0.82         = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.61/0.82      inference('demod', [status(thm)], ['172', '173', '174', '175'])).
% 0.61/0.82  thf('177', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 0.61/0.82      inference('demod', [status(thm)], ['82', '107'])).
% 0.61/0.82  thf('178', plain,
% 0.61/0.82      (![X7 : $i, X8 : $i]:
% 0.61/0.82         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.61/0.82           = (k2_xboole_0 @ X7 @ X8))),
% 0.61/0.82      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.82  thf('179', plain,
% 0.61/0.82      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.61/0.82      inference('sup+', [status(thm)], ['177', '178'])).
% 0.61/0.82  thf('180', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.61/0.82      inference('demod', [status(thm)], ['29', '30'])).
% 0.61/0.82  thf('181', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.61/0.82      inference('demod', [status(thm)], ['179', '180'])).
% 0.61/0.82  thf('182', plain,
% 0.61/0.82      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_C)) = (sk_A))),
% 0.61/0.82      inference('demod', [status(thm)], ['176', '181'])).
% 0.61/0.82  thf('183', plain, (((k4_xboole_0 @ sk_D @ sk_C) = (sk_A))),
% 0.61/0.82      inference('demod', [status(thm)], ['163', '164'])).
% 0.61/0.82  thf('184', plain,
% 0.61/0.82      (![X22 : $i, X23 : $i]:
% 0.61/0.82         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 0.61/0.82           = (X22))),
% 0.61/0.82      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.61/0.82  thf('185', plain,
% 0.61/0.82      (((k2_xboole_0 @ (k3_xboole_0 @ sk_D @ sk_C) @ sk_A) = (sk_D))),
% 0.61/0.82      inference('sup+', [status(thm)], ['183', '184'])).
% 0.61/0.82  thf('186', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.82  thf('187', plain,
% 0.61/0.82      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_C)) = (sk_D))),
% 0.61/0.82      inference('demod', [status(thm)], ['185', '186'])).
% 0.61/0.82  thf('188', plain, (((sk_A) = (sk_D))),
% 0.61/0.82      inference('sup+', [status(thm)], ['182', '187'])).
% 0.61/0.82  thf('189', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.61/0.82      inference('demod', [status(thm)], ['152', '188'])).
% 0.61/0.82  thf('190', plain, (((sk_C) = (sk_B))),
% 0.61/0.82      inference('sup+', [status(thm)], ['151', '189'])).
% 0.61/0.82  thf('191', plain, (((sk_C) != (sk_B))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('192', plain, ($false),
% 0.61/0.82      inference('simplify_reflect-', [status(thm)], ['190', '191'])).
% 0.61/0.82  
% 0.61/0.82  % SZS output end Refutation
% 0.61/0.82  
% 0.61/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
