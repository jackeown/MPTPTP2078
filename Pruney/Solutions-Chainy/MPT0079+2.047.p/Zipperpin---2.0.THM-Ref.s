%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N1YTL2jkgC

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:03 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  204 (1972 expanded)
%              Number of leaves         :   24 ( 669 expanded)
%              Depth                    :   28
%              Number of atoms          : 1487 (15219 expanded)
%              Number of equality atoms :  183 (1875 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf('0',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
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

thf('4',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_C_1 @ sk_D ) )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_D )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_D ) @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_D ) @ sk_B_1 ) @ sk_A )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_D @ k1_xboole_0 ) @ sk_B_1 ) @ sk_A )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['12','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) )
    = sk_D ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
    = sk_D ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_D )
    = ( k3_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('48',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_D @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf('55',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('56',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
    = sk_B_1 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_B_1 )
    = ( k3_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('62',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_B_1 )
    = ( k3_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf('64',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('66',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('68',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
    = sk_D ),
    inference(demod,[status(thm)],['33','40'])).

thf('69',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['28','52','53','66','67','68'])).

thf('70',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('72',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('76',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('82',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','73'])).

thf('83',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('85',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['69','85'])).

thf('87',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('88',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('90',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('91',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('92',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['86','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ X0 )
      = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C_1 )
    = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('99',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('100',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['108','109','112'])).

thf('114',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','113'])).

thf('115',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('116',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['114','117'])).

thf('119',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['76','77'])).

thf('120',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('121',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['76','77'])).

thf('122',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('124',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('126',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('128',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['118','119','120','121','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('131',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('133',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('135',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_C_1 )
    = ( k4_xboole_0 @ sk_D @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['133','136'])).

thf('138',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['118','119','120','121','128'])).

thf('139',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['131','132','137','138'])).

thf('140',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['76','77'])).

thf('141',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['139','140'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('142',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('143',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('147',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['142','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('151',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('152',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['149','150','157','158','159','160'])).

thf('162',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['141','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('164',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['69','85'])).

thf('166',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('167',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('169',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['164','169'])).

thf('171',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','170'])).

thf('172',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('173',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['118','119','120','121','128'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('176',plain,(
    sk_C_1 = sk_B_1 ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,(
    sk_C_1 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['176','177'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N1YTL2jkgC
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:03:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.77/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.99  % Solved by: fo/fo7.sh
% 0.77/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.99  % done 732 iterations in 0.524s
% 0.77/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.99  % SZS output start Refutation
% 0.77/0.99  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.77/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.99  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.77/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.77/0.99  thf(sk_B_type, type, sk_B: $i > $i).
% 0.77/0.99  thf(sk_D_type, type, sk_D: $i).
% 0.77/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(t72_xboole_1, conjecture,
% 0.77/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.99     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.77/0.99         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.77/0.99       ( ( C ) = ( B ) ) ))).
% 0.77/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.99    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.99        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.77/0.99            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.77/0.99          ( ( C ) = ( B ) ) ) )),
% 0.77/0.99    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.77/0.99  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(symmetry_r1_xboole_0, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.77/0.99  thf('1', plain,
% 0.77/0.99      (![X2 : $i, X3 : $i]:
% 0.77/0.99         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.77/0.99      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.77/0.99  thf('2', plain, ((r1_xboole_0 @ sk_B_1 @ sk_D)),
% 0.77/0.99      inference('sup-', [status(thm)], ['0', '1'])).
% 0.77/0.99  thf(t7_xboole_0, axiom,
% 0.77/0.99    (![A:$i]:
% 0.77/0.99     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.77/0.99          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.77/0.99  thf('3', plain,
% 0.77/0.99      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.77/0.99      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.77/0.99  thf(t4_xboole_0, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.77/0.99            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.77/0.99       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.77/0.99            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.77/0.99  thf('4', plain,
% 0.77/0.99      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.77/0.99         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.77/0.99          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.77/0.99      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.77/0.99  thf('5', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['3', '4'])).
% 0.77/0.99  thf('6', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['2', '5'])).
% 0.77/0.99  thf('7', plain,
% 0.77/0.99      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(commutativity_k2_xboole_0, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.77/0.99  thf('8', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('9', plain,
% 0.77/0.99      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.77/0.99      inference('demod', [status(thm)], ['7', '8'])).
% 0.77/0.99  thf(t3_boole, axiom,
% 0.77/0.99    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.77/0.99  thf('10', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.77/0.99      inference('cnf', [status(esa)], [t3_boole])).
% 0.77/0.99  thf(t48_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.77/0.99  thf('11', plain,
% 0.77/0.99      (![X19 : $i, X20 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.77/0.99           = (k3_xboole_0 @ X19 @ X20))),
% 0.77/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.99  thf('12', plain,
% 0.77/0.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['10', '11'])).
% 0.77/0.99  thf('13', plain,
% 0.77/0.99      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.77/0.99      inference('demod', [status(thm)], ['7', '8'])).
% 0.77/0.99  thf(t40_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.77/0.99  thf('14', plain,
% 0.77/0.99      (![X12 : $i, X13 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.77/0.99           = (k4_xboole_0 @ X12 @ X13))),
% 0.77/0.99      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.77/0.99  thf('15', plain,
% 0.77/0.99      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D)
% 0.77/0.99         = (k4_xboole_0 @ sk_C_1 @ sk_D))),
% 0.77/0.99      inference('sup+', [status(thm)], ['13', '14'])).
% 0.77/0.99  thf(t39_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.99  thf('16', plain,
% 0.77/0.99      (![X9 : $i, X10 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.77/0.99           = (k2_xboole_0 @ X9 @ X10))),
% 0.77/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.77/0.99  thf('17', plain,
% 0.77/0.99      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_C_1 @ sk_D))
% 0.77/0.99         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['15', '16'])).
% 0.77/0.99  thf('18', plain,
% 0.77/0.99      (![X9 : $i, X10 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.77/0.99           = (k2_xboole_0 @ X9 @ X10))),
% 0.77/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.77/0.99  thf('19', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('20', plain,
% 0.77/0.99      (((k2_xboole_0 @ sk_C_1 @ sk_D)
% 0.77/0.99         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.77/0.99      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.77/0.99  thf('21', plain,
% 0.77/0.99      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.77/0.99      inference('demod', [status(thm)], ['7', '8'])).
% 0.77/0.99  thf('22', plain,
% 0.77/0.99      (((k2_xboole_0 @ sk_B_1 @ sk_A)
% 0.77/0.99         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.77/0.99      inference('demod', [status(thm)], ['20', '21'])).
% 0.77/0.99  thf(t41_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.77/0.99       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.77/0.99  thf('23', plain,
% 0.77/0.99      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.77/0.99           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.77/0.99  thf('24', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_D) @ 
% 0.77/0.99           (k2_xboole_0 @ sk_B_1 @ sk_A))
% 0.77/0.99           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['22', '23'])).
% 0.77/0.99  thf('25', plain,
% 0.77/0.99      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.77/0.99           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.77/0.99  thf('26', plain,
% 0.77/0.99      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.77/0.99           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.77/0.99  thf('27', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_D) @ sk_B_1) @ 
% 0.77/0.99           sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B_1) @ sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.77/0.99  thf('28', plain,
% 0.77/0.99      (((k4_xboole_0 @ 
% 0.77/0.99         (k4_xboole_0 @ (k3_xboole_0 @ sk_D @ k1_xboole_0) @ sk_B_1) @ sk_A)
% 0.77/0.99         = (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B_1) @ sk_A))),
% 0.77/0.99      inference('sup+', [status(thm)], ['12', '27'])).
% 0.77/0.99  thf('29', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('30', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['3', '4'])).
% 0.77/0.99  thf('31', plain, (((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['29', '30'])).
% 0.77/0.99  thf(t51_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.77/0.99       ( A ) ))).
% 0.77/0.99  thf('32', plain,
% 0.77/0.99      (![X24 : $i, X25 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 0.77/0.99           = (X24))),
% 0.77/0.99      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.77/0.99  thf('33', plain,
% 0.77/0.99      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B_1)) = (sk_D))),
% 0.77/0.99      inference('sup+', [status(thm)], ['31', '32'])).
% 0.77/0.99  thf('34', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.77/0.99      inference('cnf', [status(esa)], [t3_boole])).
% 0.77/0.99  thf('35', plain,
% 0.77/0.99      (![X12 : $i, X13 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.77/0.99           = (k4_xboole_0 @ X12 @ X13))),
% 0.77/0.99      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.77/0.99  thf('36', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['34', '35'])).
% 0.77/0.99  thf('37', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.77/0.99      inference('cnf', [status(esa)], [t3_boole])).
% 0.77/0.99  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.77/0.99      inference('demod', [status(thm)], ['36', '37'])).
% 0.77/0.99  thf('39', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['38', '39'])).
% 0.77/0.99  thf('41', plain, (((k4_xboole_0 @ sk_D @ sk_B_1) = (sk_D))),
% 0.77/0.99      inference('demod', [status(thm)], ['33', '40'])).
% 0.77/0.99  thf('42', plain,
% 0.77/0.99      (![X19 : $i, X20 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.77/0.99           = (k3_xboole_0 @ X19 @ X20))),
% 0.77/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.99  thf('43', plain,
% 0.77/0.99      (((k4_xboole_0 @ sk_D @ sk_D) = (k3_xboole_0 @ sk_D @ sk_B_1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['41', '42'])).
% 0.77/0.99  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['38', '39'])).
% 0.77/0.99  thf('45', plain,
% 0.77/0.99      (![X12 : $i, X13 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.77/0.99           = (k4_xboole_0 @ X12 @ X13))),
% 0.77/0.99      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.77/0.99  thf('46', plain,
% 0.77/0.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['44', '45'])).
% 0.77/0.99  thf('47', plain, (((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['29', '30'])).
% 0.77/0.99  thf('48', plain, (((k4_xboole_0 @ k1_xboole_0 @ sk_D) = (k1_xboole_0))),
% 0.77/0.99      inference('demod', [status(thm)], ['43', '46', '47'])).
% 0.77/0.99  thf('49', plain,
% 0.77/0.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['10', '11'])).
% 0.77/0.99  thf('50', plain,
% 0.77/0.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['44', '45'])).
% 0.77/0.99  thf('51', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['49', '50'])).
% 0.77/0.99  thf('52', plain, (((k3_xboole_0 @ sk_D @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.99      inference('demod', [status(thm)], ['48', '51'])).
% 0.77/0.99  thf('53', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['49', '50'])).
% 0.77/0.99  thf('54', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['2', '5'])).
% 0.77/0.99  thf('55', plain,
% 0.77/0.99      (![X24 : $i, X25 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 0.77/0.99           = (X24))),
% 0.77/0.99      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.77/0.99  thf('56', plain,
% 0.77/0.99      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_D)) = (sk_B_1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['54', '55'])).
% 0.77/0.99  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['38', '39'])).
% 0.77/0.99  thf('58', plain, (((k4_xboole_0 @ sk_B_1 @ sk_D) = (sk_B_1))),
% 0.77/0.99      inference('demod', [status(thm)], ['56', '57'])).
% 0.77/0.99  thf('59', plain,
% 0.77/0.99      (![X19 : $i, X20 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.77/0.99           = (k3_xboole_0 @ X19 @ X20))),
% 0.77/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.99  thf('60', plain,
% 0.77/0.99      (((k4_xboole_0 @ sk_B_1 @ sk_B_1) = (k3_xboole_0 @ sk_B_1 @ sk_D))),
% 0.77/0.99      inference('sup+', [status(thm)], ['58', '59'])).
% 0.77/0.99  thf('61', plain,
% 0.77/0.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['44', '45'])).
% 0.77/0.99  thf('62', plain,
% 0.77/0.99      (((k4_xboole_0 @ k1_xboole_0 @ sk_B_1) = (k3_xboole_0 @ sk_B_1 @ sk_D))),
% 0.77/0.99      inference('demod', [status(thm)], ['60', '61'])).
% 0.77/0.99  thf('63', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['2', '5'])).
% 0.77/0.99  thf('64', plain, (((k4_xboole_0 @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['62', '63'])).
% 0.77/0.99  thf('65', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['49', '50'])).
% 0.77/0.99  thf('66', plain, (((k3_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.99      inference('demod', [status(thm)], ['64', '65'])).
% 0.77/0.99  thf('67', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['49', '50'])).
% 0.77/0.99  thf('68', plain, (((k4_xboole_0 @ sk_D @ sk_B_1) = (sk_D))),
% 0.77/0.99      inference('demod', [status(thm)], ['33', '40'])).
% 0.77/0.99  thf('69', plain,
% 0.77/0.99      (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['28', '52', '53', '66', '67', '68'])).
% 0.77/0.99  thf('70', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('71', plain,
% 0.77/0.99      (![X2 : $i, X3 : $i]:
% 0.77/0.99         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.77/0.99      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.77/0.99  thf('72', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.77/0.99      inference('sup-', [status(thm)], ['70', '71'])).
% 0.77/0.99  thf('73', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['3', '4'])).
% 0.77/0.99  thf('74', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['72', '73'])).
% 0.77/0.99  thf('75', plain,
% 0.77/0.99      (![X24 : $i, X25 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 0.77/0.99           = (X24))),
% 0.77/0.99      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.77/0.99  thf('76', plain,
% 0.77/0.99      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_1)) = (sk_A))),
% 0.77/0.99      inference('sup+', [status(thm)], ['74', '75'])).
% 0.77/0.99  thf('77', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['38', '39'])).
% 0.77/0.99  thf('78', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['76', '77'])).
% 0.77/0.99  thf('79', plain,
% 0.77/0.99      (![X19 : $i, X20 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.77/0.99           = (k3_xboole_0 @ X19 @ X20))),
% 0.77/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.99  thf('80', plain,
% 0.77/0.99      (((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['78', '79'])).
% 0.77/0.99  thf('81', plain,
% 0.77/0.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['44', '45'])).
% 0.77/0.99  thf('82', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['72', '73'])).
% 0.77/0.99  thf('83', plain, (((k4_xboole_0 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.77/0.99      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.77/0.99  thf('84', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['49', '50'])).
% 0.77/0.99  thf('85', plain, (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.99      inference('demod', [status(thm)], ['83', '84'])).
% 0.77/0.99  thf('86', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['69', '85'])).
% 0.77/0.99  thf('87', plain,
% 0.77/0.99      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.77/0.99           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.77/0.99  thf('88', plain,
% 0.77/0.99      (![X9 : $i, X10 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.77/0.99           = (k2_xboole_0 @ X9 @ X10))),
% 0.77/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.77/0.99  thf('89', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.77/0.99           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.77/0.99           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.77/0.99      inference('sup+', [status(thm)], ['87', '88'])).
% 0.77/0.99  thf(t4_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.77/0.99       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.77/0.99  thf('90', plain,
% 0.77/0.99      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X23)
% 0.77/0.99           = (k2_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.77/0.99  thf('91', plain,
% 0.77/0.99      (![X9 : $i, X10 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.77/0.99           = (k2_xboole_0 @ X9 @ X10))),
% 0.77/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.77/0.99  thf('92', plain,
% 0.77/0.99      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X23)
% 0.77/0.99           = (k2_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.77/0.99  thf('93', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))
% 0.77/0.99           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 0.77/0.99      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.77/0.99  thf('94', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.77/0.99           = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_D)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['86', '93'])).
% 0.77/0.99  thf('95', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.77/0.99      inference('demod', [status(thm)], ['36', '37'])).
% 0.77/0.99  thf('96', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ sk_A @ X0)
% 0.77/0.99           = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_D)))),
% 0.77/0.99      inference('demod', [status(thm)], ['94', '95'])).
% 0.77/0.99  thf('97', plain,
% 0.77/0.99      (((k2_xboole_0 @ sk_A @ sk_C_1)
% 0.77/0.99         = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['9', '96'])).
% 0.77/0.99  thf('98', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('99', plain,
% 0.77/0.99      (![X12 : $i, X13 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.77/0.99           = (k4_xboole_0 @ X12 @ X13))),
% 0.77/0.99      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.77/0.99  thf('100', plain,
% 0.77/0.99      (![X9 : $i, X10 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.77/0.99           = (k2_xboole_0 @ X9 @ X10))),
% 0.77/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.77/0.99  thf('101', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.77/0.99           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['99', '100'])).
% 0.77/0.99  thf('102', plain,
% 0.77/0.99      (![X9 : $i, X10 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.77/0.99           = (k2_xboole_0 @ X9 @ X10))),
% 0.77/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.77/0.99  thf('103', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X0 @ X1)
% 0.77/0.99           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('demod', [status(thm)], ['101', '102'])).
% 0.77/0.99  thf('104', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X0 @ X1)
% 0.77/0.99           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('demod', [status(thm)], ['101', '102'])).
% 0.77/0.99  thf('105', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1)
% 0.77/0.99           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['103', '104'])).
% 0.77/0.99  thf('106', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('107', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X0 @ X1)
% 0.77/0.99           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('demod', [status(thm)], ['101', '102'])).
% 0.77/0.99  thf('108', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X1 @ X0)
% 0.77/0.99           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.77/0.99  thf('109', plain,
% 0.77/0.99      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X23)
% 0.77/0.99           = (k2_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.77/0.99  thf('110', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('111', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X0 @ X1)
% 0.77/0.99           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('demod', [status(thm)], ['101', '102'])).
% 0.77/0.99  thf('112', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X1 @ X0)
% 0.77/0.99           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['110', '111'])).
% 0.77/0.99  thf('113', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X1 @ X0)
% 0.77/0.99           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('demod', [status(thm)], ['108', '109', '112'])).
% 0.77/0.99  thf('114', plain,
% 0.77/0.99      (((k2_xboole_0 @ sk_C_1 @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['97', '98', '113'])).
% 0.77/0.99  thf('115', plain,
% 0.77/0.99      (![X9 : $i, X10 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.77/0.99           = (k2_xboole_0 @ X9 @ X10))),
% 0.77/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.77/0.99  thf('116', plain,
% 0.77/0.99      (![X12 : $i, X13 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.77/0.99           = (k4_xboole_0 @ X12 @ X13))),
% 0.77/0.99      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.77/0.99  thf('117', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.77/0.99           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['115', '116'])).
% 0.77/0.99  thf('118', plain,
% 0.77/0.99      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ 
% 0.77/0.99         (k4_xboole_0 @ sk_A @ sk_C_1))
% 0.77/0.99         = (k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_C_1)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['114', '117'])).
% 0.77/0.99  thf('119', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['76', '77'])).
% 0.77/0.99  thf('120', plain,
% 0.77/0.99      (![X12 : $i, X13 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.77/0.99           = (k4_xboole_0 @ X12 @ X13))),
% 0.77/0.99      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.77/0.99  thf('121', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['76', '77'])).
% 0.77/0.99  thf('122', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('123', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['3', '4'])).
% 0.77/0.99  thf('124', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['122', '123'])).
% 0.77/0.99  thf('125', plain,
% 0.77/0.99      (![X24 : $i, X25 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 0.77/0.99           = (X24))),
% 0.77/0.99      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.77/0.99  thf('126', plain,
% 0.77/0.99      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_A)) = (sk_C_1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['124', '125'])).
% 0.77/0.99  thf('127', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['38', '39'])).
% 0.77/0.99  thf('128', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.77/0.99      inference('demod', [status(thm)], ['126', '127'])).
% 0.77/0.99  thf('129', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.77/0.99      inference('demod', [status(thm)], ['118', '119', '120', '121', '128'])).
% 0.77/0.99  thf('130', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.77/0.99           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['115', '116'])).
% 0.77/0.99  thf('131', plain,
% 0.77/0.99      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_C_1)
% 0.77/0.99         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['129', '130'])).
% 0.77/0.99  thf('132', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('133', plain,
% 0.77/0.99      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.77/0.99      inference('demod', [status(thm)], ['7', '8'])).
% 0.77/0.99  thf('134', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('135', plain,
% 0.77/0.99      (![X12 : $i, X13 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.77/0.99           = (k4_xboole_0 @ X12 @ X13))),
% 0.77/0.99      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.77/0.99  thf('136', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.77/0.99           = (k4_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['134', '135'])).
% 0.77/0.99  thf('137', plain,
% 0.77/0.99      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_C_1)
% 0.77/0.99         = (k4_xboole_0 @ sk_D @ sk_C_1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['133', '136'])).
% 0.77/0.99  thf('138', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.77/0.99      inference('demod', [status(thm)], ['118', '119', '120', '121', '128'])).
% 0.77/0.99  thf('139', plain,
% 0.77/0.99      (((k4_xboole_0 @ sk_D @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.77/0.99      inference('demod', [status(thm)], ['131', '132', '137', '138'])).
% 0.77/0.99  thf('140', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['76', '77'])).
% 0.77/0.99  thf('141', plain, (((k4_xboole_0 @ sk_D @ sk_C_1) = (sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['139', '140'])).
% 0.77/0.99  thf(t47_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.77/0.99  thf('142', plain,
% 0.77/0.99      (![X17 : $i, X18 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 0.77/0.99           = (k4_xboole_0 @ X17 @ X18))),
% 0.77/0.99      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.77/0.99  thf('143', plain,
% 0.77/0.99      (![X9 : $i, X10 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.77/0.99           = (k2_xboole_0 @ X9 @ X10))),
% 0.77/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.77/0.99  thf('144', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X0 @ X1)
% 0.77/0.99           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('demod', [status(thm)], ['101', '102'])).
% 0.77/0.99  thf('145', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 0.77/0.99           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['143', '144'])).
% 0.77/0.99  thf('146', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('147', plain,
% 0.77/0.99      (![X9 : $i, X10 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.77/0.99           = (k2_xboole_0 @ X9 @ X10))),
% 0.77/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.77/0.99  thf('148', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X1 @ X0)
% 0.77/0.99           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.77/0.99  thf('149', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.77/0.99           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.77/0.99              (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['142', '148'])).
% 0.77/0.99  thf('150', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('151', plain,
% 0.77/0.99      (![X17 : $i, X18 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 0.77/0.99           = (k4_xboole_0 @ X17 @ X18))),
% 0.77/0.99      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.77/0.99  thf('152', plain,
% 0.77/0.99      (![X9 : $i, X10 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.77/0.99           = (k2_xboole_0 @ X9 @ X10))),
% 0.77/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.77/0.99  thf('153', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.77/0.99           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['151', '152'])).
% 0.77/0.99  thf('154', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('155', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.77/0.99           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('demod', [status(thm)], ['153', '154'])).
% 0.77/0.99  thf('156', plain,
% 0.77/0.99      (![X24 : $i, X25 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 0.77/0.99           = (X24))),
% 0.77/0.99      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.77/0.99  thf('157', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['155', '156'])).
% 0.77/0.99  thf('158', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('159', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['155', '156'])).
% 0.77/0.99  thf('160', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('161', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('demod', [status(thm)],
% 0.77/0.99                ['149', '150', '157', '158', '159', '160'])).
% 0.77/0.99  thf('162', plain, (((sk_D) = (k2_xboole_0 @ sk_D @ sk_A))),
% 0.77/0.99      inference('sup+', [status(thm)], ['141', '161'])).
% 0.77/0.99  thf('163', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('164', plain, (((sk_D) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.77/0.99      inference('demod', [status(thm)], ['162', '163'])).
% 0.77/0.99  thf('165', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['69', '85'])).
% 0.77/0.99  thf('166', plain,
% 0.77/0.99      (![X9 : $i, X10 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.77/0.99           = (k2_xboole_0 @ X9 @ X10))),
% 0.77/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.77/0.99  thf('167', plain,
% 0.77/0.99      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.77/0.99      inference('sup+', [status(thm)], ['165', '166'])).
% 0.77/0.99  thf('168', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.77/0.99      inference('demod', [status(thm)], ['36', '37'])).
% 0.77/0.99  thf('169', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.77/0.99      inference('demod', [status(thm)], ['167', '168'])).
% 0.77/0.99  thf('170', plain, (((sk_A) = (sk_D))),
% 0.77/0.99      inference('sup+', [status(thm)], ['164', '169'])).
% 0.77/0.99  thf('171', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.77/0.99      inference('demod', [status(thm)], ['6', '170'])).
% 0.77/0.99  thf('172', plain,
% 0.77/0.99      (![X24 : $i, X25 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 0.77/0.99           = (X24))),
% 0.77/0.99      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.77/0.99  thf('173', plain,
% 0.77/0.99      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_A)) = (sk_B_1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['171', '172'])).
% 0.77/0.99  thf('174', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.77/0.99      inference('demod', [status(thm)], ['118', '119', '120', '121', '128'])).
% 0.77/0.99  thf('175', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['38', '39'])).
% 0.77/0.99  thf('176', plain, (((sk_C_1) = (sk_B_1))),
% 0.77/0.99      inference('demod', [status(thm)], ['173', '174', '175'])).
% 0.77/0.99  thf('177', plain, (((sk_C_1) != (sk_B_1))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('178', plain, ($false),
% 0.77/0.99      inference('simplify_reflect-', [status(thm)], ['176', '177'])).
% 0.77/0.99  
% 0.77/0.99  % SZS output end Refutation
% 0.77/0.99  
% 0.77/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
