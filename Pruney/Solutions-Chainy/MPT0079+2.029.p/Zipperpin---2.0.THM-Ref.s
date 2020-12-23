%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VjgWxpGRyu

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:00 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 420 expanded)
%              Number of leaves         :   22 ( 142 expanded)
%              Depth                    :   17
%              Number of atoms          :  656 (3232 expanded)
%              Number of equality atoms :   78 ( 406 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(t71_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf('3',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_xboole_0 @ X31 @ X32 )
      | ( ( k2_xboole_0 @ X31 @ X32 )
       != ( k2_xboole_0 @ X33 @ X32 ) )
      | ~ ( r1_xboole_0 @ X33 @ X32 )
      | ( X31 = X33 ) ) ),
    inference(cnf,[status(esa)],[t71_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B @ sk_A )
       != ( k2_xboole_0 @ X0 @ sk_D ) )
      | ( sk_C = X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ~ ( r1_xboole_0 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','11'])).

thf('13',plain,(
    r1_tarski @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('25',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('29',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_D ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['24','31'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('33',plain,(
    ! [X27: $i,X28: $i,X30: $i] :
      ( ( r1_xboole_0 @ X27 @ X30 )
      | ~ ( r1_xboole_0 @ X27 @ ( k2_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference('sup-',[status(thm)],['5','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B @ sk_A )
       != ( k2_xboole_0 @ X0 @ sk_D ) )
      | ( sk_C = X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['4','35'])).

thf('37',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('39',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('43',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_A ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','11'])).

thf('53',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('59',plain,
    ( ( k2_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('63',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['24','31'])).

thf('65',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['63','64'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B @ sk_A )
       != ( k2_xboole_0 @ X0 @ sk_A ) )
      | ( sk_C = X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','65','66'])).

thf('68',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_A )
    | ( sk_C = sk_B ) ),
    inference(eq_res,[status(thm)],['67'])).

thf('69',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('71',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['63','64'])).

thf('73',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    sk_C = sk_B ),
    inference(demod,[status(thm)],['68','73'])).

thf('75',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VjgWxpGRyu
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:46:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 981 iterations in 0.326s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.79  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(t72_xboole_1, conjecture,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.59/0.79         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.59/0.79       ( ( C ) = ( B ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.59/0.79            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.59/0.79          ( ( C ) = ( B ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.59/0.79  thf('0', plain,
% 0.59/0.79      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(commutativity_k2_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.59/0.79  thf('1', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.79  thf('2', plain,
% 0.59/0.79      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['0', '1'])).
% 0.59/0.79  thf(t71_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.59/0.79         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.59/0.79       ( ( A ) = ( C ) ) ))).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.59/0.79         (~ (r1_xboole_0 @ X31 @ X32)
% 0.59/0.79          | ((k2_xboole_0 @ X31 @ X32) != (k2_xboole_0 @ X33 @ X32))
% 0.59/0.79          | ~ (r1_xboole_0 @ X33 @ X32)
% 0.59/0.79          | ((X31) = (X33)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t71_xboole_1])).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (((k2_xboole_0 @ sk_B @ sk_A) != (k2_xboole_0 @ X0 @ sk_D))
% 0.59/0.79          | ((sk_C) = (X0))
% 0.59/0.79          | ~ (r1_xboole_0 @ X0 @ sk_D)
% 0.59/0.79          | ~ (r1_xboole_0 @ sk_C @ sk_D))),
% 0.59/0.79      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.79  thf('5', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['0', '1'])).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.79  thf(t46_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (![X18 : $i, X19 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (k1_xboole_0))),
% 0.59/0.79      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.59/0.79  thf(l32_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X7 : $i, X8 : $i]:
% 0.59/0.79         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 0.59/0.79      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.79          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.79      inference('simplify', [status(thm)], ['10'])).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['7', '11'])).
% 0.59/0.79  thf('13', plain, ((r1_tarski @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['6', '12'])).
% 0.59/0.79  thf('14', plain,
% 0.59/0.79      (![X7 : $i, X9 : $i]:
% 0.59/0.79         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.59/0.79      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (((k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.79  thf(t41_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.79       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.59/0.79           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (((k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A) = (k1_xboole_0))),
% 0.59/0.79      inference('demod', [status(thm)], ['15', '16'])).
% 0.59/0.79  thf(t39_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (![X13 : $i, X14 : $i]:
% 0.59/0.79         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.59/0.79           = (k2_xboole_0 @ X13 @ X14))),
% 0.59/0.79      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 0.59/0.79         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['17', '18'])).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.79  thf(t1_boole, axiom,
% 0.59/0.79    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.79  thf('22', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.59/0.79      inference('cnf', [status(esa)], [t1_boole])).
% 0.59/0.79  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.79  thf('24', plain,
% 0.59/0.79      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)))),
% 0.59/0.79      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.59/0.79  thf('25', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(d7_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.59/0.79       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.79  thf('26', plain,
% 0.59/0.79      (![X2 : $i, X3 : $i]:
% 0.59/0.79         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.59/0.79      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.59/0.79  thf('27', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.79  thf(t51_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.59/0.79       ( A ) ))).
% 0.59/0.79  thf('28', plain,
% 0.59/0.79      (![X25 : $i, X26 : $i]:
% 0.59/0.79         ((k2_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ (k4_xboole_0 @ X25 @ X26))
% 0.59/0.79           = (X25))),
% 0.59/0.79      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.59/0.79  thf('29', plain,
% 0.59/0.79      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_D))),
% 0.59/0.79      inference('sup+', [status(thm)], ['27', '28'])).
% 0.59/0.79  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.79  thf('31', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.79  thf('32', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['24', '31'])).
% 0.59/0.79  thf(t70_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.59/0.79            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.59/0.79       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.59/0.79            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.59/0.79  thf('33', plain,
% 0.59/0.79      (![X27 : $i, X28 : $i, X30 : $i]:
% 0.59/0.79         ((r1_xboole_0 @ X27 @ X30)
% 0.59/0.79          | ~ (r1_xboole_0 @ X27 @ (k2_xboole_0 @ X28 @ X30)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.59/0.79  thf('34', plain,
% 0.59/0.79      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ sk_A) | (r1_xboole_0 @ X0 @ sk_D))),
% 0.59/0.79      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.79  thf('35', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '34'])).
% 0.59/0.79  thf('36', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (((k2_xboole_0 @ sk_B @ sk_A) != (k2_xboole_0 @ X0 @ sk_D))
% 0.59/0.79          | ((sk_C) = (X0))
% 0.59/0.79          | ~ (r1_xboole_0 @ X0 @ sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['4', '35'])).
% 0.59/0.79  thf('37', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(symmetry_r1_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.59/0.79  thf('38', plain,
% 0.59/0.79      (![X5 : $i, X6 : $i]:
% 0.59/0.79         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.59/0.79      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.59/0.79  thf('39', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.59/0.79      inference('sup-', [status(thm)], ['37', '38'])).
% 0.59/0.79  thf('40', plain,
% 0.59/0.79      (![X2 : $i, X3 : $i]:
% 0.59/0.79         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.59/0.79      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.59/0.79  thf('41', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.79  thf('42', plain,
% 0.59/0.79      (![X25 : $i, X26 : $i]:
% 0.59/0.79         ((k2_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ (k4_xboole_0 @ X25 @ X26))
% 0.59/0.79           = (X25))),
% 0.59/0.79      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.59/0.79  thf('43', plain,
% 0.59/0.79      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['41', '42'])).
% 0.59/0.79  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.79  thf('45', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['43', '44'])).
% 0.59/0.79  thf('46', plain,
% 0.59/0.79      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['0', '1'])).
% 0.59/0.79  thf('47', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.59/0.79           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.59/0.79  thf('48', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 0.59/0.79           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['46', '47'])).
% 0.59/0.79  thf('49', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.59/0.79           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.59/0.79  thf('50', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 0.59/0.79           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['48', '49'])).
% 0.59/0.79  thf('51', plain,
% 0.59/0.79      (((k4_xboole_0 @ sk_A @ sk_D)
% 0.59/0.79         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['45', '50'])).
% 0.59/0.79  thf('52', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['7', '11'])).
% 0.59/0.79  thf('53', plain,
% 0.59/0.79      (![X7 : $i, X9 : $i]:
% 0.59/0.79         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.59/0.79      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.79  thf('54', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['52', '53'])).
% 0.59/0.79  thf('55', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.59/0.79           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.59/0.79  thf('56', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.59/0.79      inference('demod', [status(thm)], ['54', '55'])).
% 0.59/0.79  thf('57', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 0.59/0.79      inference('demod', [status(thm)], ['51', '56'])).
% 0.59/0.79  thf('58', plain,
% 0.59/0.79      (![X13 : $i, X14 : $i]:
% 0.59/0.79         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.59/0.79           = (k2_xboole_0 @ X13 @ X14))),
% 0.59/0.79      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.79  thf('59', plain,
% 0.59/0.79      (((k2_xboole_0 @ sk_D @ k1_xboole_0) = (k2_xboole_0 @ sk_D @ sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['57', '58'])).
% 0.59/0.79  thf('60', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.79  thf('61', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.79  thf('62', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.79  thf('63', plain, (((sk_D) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.59/0.79  thf('64', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['24', '31'])).
% 0.59/0.79  thf('65', plain, (((sk_A) = (sk_D))),
% 0.59/0.79      inference('sup+', [status(thm)], ['63', '64'])).
% 0.59/0.79  thf('66', plain, (((sk_A) = (sk_D))),
% 0.59/0.79      inference('sup+', [status(thm)], ['63', '64'])).
% 0.59/0.79  thf('67', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (((k2_xboole_0 @ sk_B @ sk_A) != (k2_xboole_0 @ X0 @ sk_A))
% 0.59/0.79          | ((sk_C) = (X0))
% 0.59/0.79          | ~ (r1_xboole_0 @ X0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['36', '65', '66'])).
% 0.59/0.79  thf('68', plain, ((~ (r1_xboole_0 @ sk_B @ sk_A) | ((sk_C) = (sk_B)))),
% 0.59/0.79      inference('eq_res', [status(thm)], ['67'])).
% 0.59/0.79  thf('69', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('70', plain,
% 0.59/0.79      (![X5 : $i, X6 : $i]:
% 0.59/0.79         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.59/0.79      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.59/0.79  thf('71', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.59/0.79      inference('sup-', [status(thm)], ['69', '70'])).
% 0.59/0.79  thf('72', plain, (((sk_A) = (sk_D))),
% 0.59/0.79      inference('sup+', [status(thm)], ['63', '64'])).
% 0.59/0.79  thf('73', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.59/0.79      inference('demod', [status(thm)], ['71', '72'])).
% 0.59/0.79  thf('74', plain, (((sk_C) = (sk_B))),
% 0.59/0.79      inference('demod', [status(thm)], ['68', '73'])).
% 0.59/0.79  thf('75', plain, (((sk_C) != (sk_B))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('76', plain, ($false),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
