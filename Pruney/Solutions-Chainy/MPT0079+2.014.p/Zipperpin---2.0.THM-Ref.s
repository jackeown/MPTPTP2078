%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c4ZgJgTtrI

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:58 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 722 expanded)
%              Number of leaves         :   21 ( 242 expanded)
%              Depth                    :   21
%              Number of atoms          : 1225 (5777 expanded)
%              Number of equality atoms :  175 ( 805 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

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
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = sk_B ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10 = X9 )
      | ( ( k4_xboole_0 @ X10 @ X9 )
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
       != ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ sk_B )
       != ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['10','13'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ sk_B )
       != ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) ) )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_D ) @ sk_B )
       != ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) ) )
      | ( ( k4_xboole_0 @ X0 @ sk_D )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_D ) )
       != ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) ) )
      | ( ( k4_xboole_0 @ X0 @ sk_D )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('30',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_A ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
       != ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ sk_A )
       != ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ sk_A )
       != ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
      | ( X0 = sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ sk_D @ sk_A )
     != ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) )
    | ( sk_D = sk_A ) ),
    inference('sup-',[status(thm)],['27','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ sk_D @ sk_A )
     != k1_xboole_0 )
    | ( sk_D = sk_A ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
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
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('57',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_D ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['52','53','54','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = sk_A ) ),
    inference(demod,[status(thm)],['45','62'])).

thf('64',plain,(
    sk_D = sk_A ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    sk_D = sk_A ),
    inference(simplify,[status(thm)],['63'])).

thf('66',plain,(
    sk_D = sk_A ),
    inference(simplify,[status(thm)],['63'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
       != ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) )
      | ( ( k4_xboole_0 @ X0 @ sk_A )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['24','64','65','66'])).

thf('68',plain,
    ( ( k1_xboole_0
     != ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) )
    | ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['2','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('70',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('71',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('79',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('81',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ sk_A )
       != ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
      | ( X0 = sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_A )
       != ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
      | ( ( k4_xboole_0 @ X0 @ sk_C )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_C @ sk_A ) )
       != ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
      | ( ( k4_xboole_0 @ X0 @ sk_C )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('87',plain,(
    sk_D = sk_A ),
    inference(simplify,[status(thm)],['63'])).

thf('88',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('90',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
       != ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( ( k4_xboole_0 @ X0 @ sk_C )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['85','88','91'])).

thf('93',plain,
    ( ( k1_xboole_0
     != ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) )
    | ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['80','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('95',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_C )
      = sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_C )
    = sk_A ),
    inference(simplify,[status(thm)],['95'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('97',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('98',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_A )
    = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('100',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
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

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('106',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('109',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('111',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('112',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = sk_C ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('114',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_B ) )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['109','116'])).

thf('118',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('119',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('120',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['112','113'])).

thf('121',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('123',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('129',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('134',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('135',plain,(
    ! [X0: $i] :
      ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['98','99','135'])).

thf('137',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['68','77','78','79','136'])).

thf('138',plain,(
    sk_C = sk_B ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['138','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c4ZgJgTtrI
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.99/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.21  % Solved by: fo/fo7.sh
% 0.99/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.21  % done 1436 iterations in 0.717s
% 0.99/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.21  % SZS output start Refutation
% 0.99/1.21  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.99/1.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.21  thf(sk_C_type, type, sk_C: $i).
% 0.99/1.21  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.99/1.21  thf(sk_D_type, type, sk_D: $i).
% 0.99/1.21  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.21  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.21  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.21  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.99/1.21  thf(t1_boole, axiom,
% 0.99/1.21    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.99/1.21  thf('0', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.99/1.21      inference('cnf', [status(esa)], [t1_boole])).
% 0.99/1.21  thf(t46_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.99/1.21  thf('1', plain,
% 0.99/1.21      (![X17 : $i, X18 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (k1_xboole_0))),
% 0.99/1.21      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.99/1.21  thf('2', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['0', '1'])).
% 0.99/1.21  thf(t39_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.99/1.21  thf('3', plain,
% 0.99/1.21      (![X11 : $i, X12 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.99/1.21           = (k2_xboole_0 @ X11 @ X12))),
% 0.99/1.21      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.99/1.21  thf(t72_xboole_1, conjecture,
% 0.99/1.21    (![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.21     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.99/1.21         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.99/1.21       ( ( C ) = ( B ) ) ))).
% 0.99/1.21  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.21    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.21        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.99/1.21            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.99/1.21          ( ( C ) = ( B ) ) ) )),
% 0.99/1.21    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.99/1.21  thf('4', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf(d7_xboole_0, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.99/1.21       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.99/1.21  thf('5', plain,
% 0.99/1.21      (![X4 : $i, X5 : $i]:
% 0.99/1.21         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.99/1.21      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.99/1.21  thf('6', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.99/1.21      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.21  thf(commutativity_k3_xboole_0, axiom,
% 0.99/1.21    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.99/1.21  thf('7', plain,
% 0.99/1.21      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.21  thf('8', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.99/1.21      inference('demod', [status(thm)], ['6', '7'])).
% 0.99/1.21  thf(t51_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.99/1.21       ( A ) ))).
% 0.99/1.21  thf('9', plain,
% 0.99/1.21      (![X21 : $i, X22 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.99/1.21           = (X21))),
% 0.99/1.21      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.99/1.21  thf('10', plain,
% 0.99/1.21      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_D)) = (sk_B))),
% 0.99/1.21      inference('sup+', [status(thm)], ['8', '9'])).
% 0.99/1.21  thf(commutativity_k2_xboole_0, axiom,
% 0.99/1.21    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.99/1.21  thf('11', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.21  thf('12', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.99/1.21      inference('cnf', [status(esa)], [t1_boole])).
% 0.99/1.21  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['11', '12'])).
% 0.99/1.21  thf('14', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 0.99/1.21      inference('demod', [status(thm)], ['10', '13'])).
% 0.99/1.21  thf(t41_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.99/1.21       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.99/1.21  thf('15', plain,
% 0.99/1.21      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.99/1.21           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.99/1.21      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.21  thf(t32_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.99/1.21       ( ( A ) = ( B ) ) ))).
% 0.99/1.21  thf('16', plain,
% 0.99/1.21      (![X9 : $i, X10 : $i]:
% 0.99/1.21         (((X10) = (X9))
% 0.99/1.21          | ((k4_xboole_0 @ X10 @ X9) != (k4_xboole_0 @ X9 @ X10)))),
% 0.99/1.21      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.99/1.21  thf('17', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.21         (((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 0.99/1.21            != (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.99/1.21          | ((X0) = (k4_xboole_0 @ X2 @ X1)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['15', '16'])).
% 0.99/1.21  thf('18', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (((k4_xboole_0 @ X0 @ sk_B)
% 0.99/1.21            != (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_D @ X0)))
% 0.99/1.21          | ((X0) = (k4_xboole_0 @ sk_B @ sk_D)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['14', '17'])).
% 0.99/1.21  thf('19', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 0.99/1.21      inference('demod', [status(thm)], ['10', '13'])).
% 0.99/1.21  thf('20', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (((k4_xboole_0 @ X0 @ sk_B)
% 0.99/1.21            != (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_D @ X0)))
% 0.99/1.21          | ((X0) = (sk_B)))),
% 0.99/1.21      inference('demod', [status(thm)], ['18', '19'])).
% 0.99/1.21  thf('21', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_D) @ sk_B)
% 0.99/1.21            != (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_D @ X0)))
% 0.99/1.21          | ((k4_xboole_0 @ X0 @ sk_D) = (sk_B)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['3', '20'])).
% 0.99/1.21  thf('22', plain,
% 0.99/1.21      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.99/1.21           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.99/1.21      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.21  thf('23', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.21  thf('24', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (((k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_D))
% 0.99/1.21            != (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_D @ X0)))
% 0.99/1.21          | ((k4_xboole_0 @ X0 @ sk_D) = (sk_B)))),
% 0.99/1.21      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.99/1.21  thf('25', plain,
% 0.99/1.21      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('26', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.21  thf('27', plain,
% 0.99/1.21      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.99/1.21      inference('demod', [status(thm)], ['25', '26'])).
% 0.99/1.21  thf('28', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('29', plain,
% 0.99/1.21      (![X4 : $i, X5 : $i]:
% 0.99/1.21         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.99/1.21      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.99/1.21  thf('30', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.99/1.21      inference('sup-', [status(thm)], ['28', '29'])).
% 0.99/1.21  thf('31', plain,
% 0.99/1.21      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.21  thf('32', plain,
% 0.99/1.21      (![X21 : $i, X22 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.99/1.21           = (X21))),
% 0.99/1.21      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.99/1.21  thf('33', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.99/1.21           = (X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['31', '32'])).
% 0.99/1.21  thf('34', plain,
% 0.99/1.21      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_A))),
% 0.99/1.21      inference('sup+', [status(thm)], ['30', '33'])).
% 0.99/1.21  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['11', '12'])).
% 0.99/1.21  thf('36', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.99/1.21      inference('demod', [status(thm)], ['34', '35'])).
% 0.99/1.21  thf('37', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.21         (((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 0.99/1.21            != (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.99/1.21          | ((X0) = (k4_xboole_0 @ X2 @ X1)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['15', '16'])).
% 0.99/1.21  thf('38', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (((k4_xboole_0 @ X0 @ sk_A)
% 0.99/1.21            != (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))
% 0.99/1.21          | ((X0) = (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['36', '37'])).
% 0.99/1.21  thf('39', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.99/1.21      inference('demod', [status(thm)], ['34', '35'])).
% 0.99/1.21  thf('40', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (((k4_xboole_0 @ X0 @ sk_A)
% 0.99/1.21            != (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))
% 0.99/1.21          | ((X0) = (sk_A)))),
% 0.99/1.21      inference('demod', [status(thm)], ['38', '39'])).
% 0.99/1.21  thf('41', plain,
% 0.99/1.21      ((((k4_xboole_0 @ sk_D @ sk_A)
% 0.99/1.21          != (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))
% 0.99/1.21        | ((sk_D) = (sk_A)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['27', '40'])).
% 0.99/1.21  thf('42', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.21  thf('43', plain,
% 0.99/1.21      (![X17 : $i, X18 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (k1_xboole_0))),
% 0.99/1.21      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.99/1.21  thf('44', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['42', '43'])).
% 0.99/1.21  thf('45', plain,
% 0.99/1.21      ((((k4_xboole_0 @ sk_D @ sk_A) != (k1_xboole_0)) | ((sk_D) = (sk_A)))),
% 0.99/1.21      inference('demod', [status(thm)], ['41', '44'])).
% 0.99/1.21  thf('46', plain,
% 0.99/1.21      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.99/1.21      inference('demod', [status(thm)], ['25', '26'])).
% 0.99/1.21  thf('47', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['42', '43'])).
% 0.99/1.21  thf('48', plain,
% 0.99/1.21      (((k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['46', '47'])).
% 0.99/1.21  thf('49', plain,
% 0.99/1.21      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.99/1.21           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.99/1.21      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.21  thf('50', plain,
% 0.99/1.21      (![X11 : $i, X12 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.99/1.21           = (k2_xboole_0 @ X11 @ X12))),
% 0.99/1.21      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.99/1.21  thf('51', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.99/1.21           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['49', '50'])).
% 0.99/1.21  thf('52', plain,
% 0.99/1.21      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 0.99/1.21         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['48', '51'])).
% 0.99/1.21  thf('53', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.21  thf('54', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['11', '12'])).
% 0.99/1.21  thf('55', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.99/1.21      inference('demod', [status(thm)], ['6', '7'])).
% 0.99/1.21  thf('56', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.99/1.21           = (X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['31', '32'])).
% 0.99/1.21  thf('57', plain,
% 0.99/1.21      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_D))),
% 0.99/1.21      inference('sup+', [status(thm)], ['55', '56'])).
% 0.99/1.21  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['11', '12'])).
% 0.99/1.21  thf('59', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 0.99/1.21      inference('demod', [status(thm)], ['57', '58'])).
% 0.99/1.21  thf('60', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.99/1.21      inference('demod', [status(thm)], ['52', '53', '54', '59'])).
% 0.99/1.21  thf('61', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['42', '43'])).
% 0.99/1.21  thf('62', plain, (((k4_xboole_0 @ sk_D @ sk_A) = (k1_xboole_0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['60', '61'])).
% 0.99/1.21  thf('63', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (sk_A)))),
% 0.99/1.21      inference('demod', [status(thm)], ['45', '62'])).
% 0.99/1.21  thf('64', plain, (((sk_D) = (sk_A))),
% 0.99/1.21      inference('simplify', [status(thm)], ['63'])).
% 0.99/1.21  thf('65', plain, (((sk_D) = (sk_A))),
% 0.99/1.21      inference('simplify', [status(thm)], ['63'])).
% 0.99/1.21  thf('66', plain, (((sk_D) = (sk_A))),
% 0.99/1.21      inference('simplify', [status(thm)], ['63'])).
% 0.99/1.21  thf('67', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (((k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.99/1.21            != (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))
% 0.99/1.21          | ((k4_xboole_0 @ X0 @ sk_A) = (sk_B)))),
% 0.99/1.21      inference('demod', [status(thm)], ['24', '64', '65', '66'])).
% 0.99/1.21  thf('68', plain,
% 0.99/1.21      ((((k1_xboole_0)
% 0.99/1.21          != (k4_xboole_0 @ sk_B @ 
% 0.99/1.21              (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A))))
% 0.99/1.21        | ((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_A) = (sk_B)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['2', '67'])).
% 0.99/1.21  thf('69', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.21  thf('70', plain,
% 0.99/1.21      (![X17 : $i, X18 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (k1_xboole_0))),
% 0.99/1.21      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.99/1.21  thf('71', plain,
% 0.99/1.21      (![X11 : $i, X12 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.99/1.21           = (k2_xboole_0 @ X11 @ X12))),
% 0.99/1.21      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.99/1.21  thf('72', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.99/1.21           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['70', '71'])).
% 0.99/1.21  thf('73', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.21  thf('74', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['11', '12'])).
% 0.99/1.21  thf('75', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.21  thf('76', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ X0 @ X1)
% 0.99/1.21           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.99/1.21      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.99/1.21  thf('77', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ X0 @ X1)
% 0.99/1.21           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['69', '76'])).
% 0.99/1.21  thf('78', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.21  thf('79', plain,
% 0.99/1.21      (![X17 : $i, X18 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (k1_xboole_0))),
% 0.99/1.21      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.99/1.21  thf('80', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['0', '1'])).
% 0.99/1.21  thf('81', plain,
% 0.99/1.21      (![X11 : $i, X12 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.99/1.21           = (k2_xboole_0 @ X11 @ X12))),
% 0.99/1.21      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.99/1.21  thf('82', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (((k4_xboole_0 @ X0 @ sk_A)
% 0.99/1.21            != (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))
% 0.99/1.21          | ((X0) = (sk_A)))),
% 0.99/1.21      inference('demod', [status(thm)], ['38', '39'])).
% 0.99/1.21  thf('83', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.99/1.21            != (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))
% 0.99/1.21          | ((k4_xboole_0 @ X0 @ sk_C) = (sk_A)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['81', '82'])).
% 0.99/1.21  thf('84', plain,
% 0.99/1.21      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.99/1.21           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.99/1.21      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.21  thf('85', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (((k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_C @ sk_A))
% 0.99/1.21            != (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))
% 0.99/1.21          | ((k4_xboole_0 @ X0 @ sk_C) = (sk_A)))),
% 0.99/1.21      inference('demod', [status(thm)], ['83', '84'])).
% 0.99/1.21  thf('86', plain,
% 0.99/1.21      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.99/1.21      inference('demod', [status(thm)], ['25', '26'])).
% 0.99/1.21  thf('87', plain, (((sk_D) = (sk_A))),
% 0.99/1.21      inference('simplify', [status(thm)], ['63'])).
% 0.99/1.21  thf('88', plain,
% 0.99/1.21      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_A))),
% 0.99/1.21      inference('demod', [status(thm)], ['86', '87'])).
% 0.99/1.21  thf('89', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.99/1.21      inference('demod', [status(thm)], ['34', '35'])).
% 0.99/1.21  thf('90', plain,
% 0.99/1.21      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.99/1.21           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.99/1.21      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.21  thf('91', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ sk_A @ X0)
% 0.99/1.21           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['89', '90'])).
% 0.99/1.21  thf('92', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (((k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.99/1.21            != (k4_xboole_0 @ sk_A @ X0))
% 0.99/1.21          | ((k4_xboole_0 @ X0 @ sk_C) = (sk_A)))),
% 0.99/1.21      inference('demod', [status(thm)], ['85', '88', '91'])).
% 0.99/1.21  thf('93', plain,
% 0.99/1.21      ((((k1_xboole_0) != (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))
% 0.99/1.21        | ((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_C) = (sk_A)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['80', '92'])).
% 0.99/1.21  thf('94', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['42', '43'])).
% 0.99/1.21  thf('95', plain,
% 0.99/1.21      ((((k1_xboole_0) != (k1_xboole_0))
% 0.99/1.21        | ((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_C) = (sk_A)))),
% 0.99/1.21      inference('demod', [status(thm)], ['93', '94'])).
% 0.99/1.21  thf('96', plain,
% 0.99/1.21      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_C) = (sk_A))),
% 0.99/1.21      inference('simplify', [status(thm)], ['95'])).
% 0.99/1.21  thf(t48_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.99/1.21  thf('97', plain,
% 0.99/1.21      (![X19 : $i, X20 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.99/1.21           = (k3_xboole_0 @ X19 @ X20))),
% 0.99/1.21      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.21  thf('98', plain,
% 0.99/1.21      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_A)
% 0.99/1.21         = (k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 0.99/1.21      inference('sup+', [status(thm)], ['96', '97'])).
% 0.99/1.21  thf('99', plain,
% 0.99/1.21      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.21  thf('100', plain,
% 0.99/1.21      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('101', plain,
% 0.99/1.21      (![X17 : $i, X18 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (k1_xboole_0))),
% 0.99/1.21      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.99/1.21  thf('102', plain,
% 0.99/1.21      (((k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['100', '101'])).
% 0.99/1.21  thf('103', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.21  thf('104', plain,
% 0.99/1.21      (((k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 0.99/1.21      inference('demod', [status(thm)], ['102', '103'])).
% 0.99/1.21  thf('105', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.99/1.21           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['49', '50'])).
% 0.99/1.21  thf('106', plain,
% 0.99/1.21      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 0.99/1.21         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['104', '105'])).
% 0.99/1.21  thf('107', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.21  thf('108', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['11', '12'])).
% 0.99/1.21  thf('109', plain,
% 0.99/1.21      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 0.99/1.21      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.99/1.21  thf('110', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.99/1.21      inference('sup-', [status(thm)], ['28', '29'])).
% 0.99/1.21  thf('111', plain,
% 0.99/1.21      (![X21 : $i, X22 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.99/1.21           = (X21))),
% 0.99/1.21      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.99/1.21  thf('112', plain,
% 0.99/1.21      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A)) = (sk_C))),
% 0.99/1.21      inference('sup+', [status(thm)], ['110', '111'])).
% 0.99/1.21  thf('113', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['11', '12'])).
% 0.99/1.21  thf('114', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.99/1.21      inference('demod', [status(thm)], ['112', '113'])).
% 0.99/1.21  thf('115', plain,
% 0.99/1.21      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.99/1.21           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.99/1.21      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.21  thf('116', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ sk_C @ X0)
% 0.99/1.21           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['114', '115'])).
% 0.99/1.21  thf('117', plain,
% 0.99/1.21      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_B))
% 0.99/1.21         = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.99/1.21      inference('sup+', [status(thm)], ['109', '116'])).
% 0.99/1.21  thf('118', plain,
% 0.99/1.21      (![X19 : $i, X20 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.99/1.21           = (k3_xboole_0 @ X19 @ X20))),
% 0.99/1.21      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.21  thf('119', plain,
% 0.99/1.21      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.21  thf('120', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.99/1.21      inference('demod', [status(thm)], ['112', '113'])).
% 0.99/1.21  thf('121', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (sk_C))),
% 0.99/1.21      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 0.99/1.21  thf('122', plain,
% 0.99/1.21      (![X21 : $i, X22 : $i]:
% 0.99/1.21         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.99/1.21           = (X21))),
% 0.99/1.21      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.99/1.21  thf('123', plain,
% 0.99/1.21      (![X17 : $i, X18 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (k1_xboole_0))),
% 0.99/1.21      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.99/1.21  thf('124', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['122', '123'])).
% 0.99/1.21  thf('125', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['121', '124'])).
% 0.99/1.21  thf('126', plain,
% 0.99/1.21      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.99/1.21           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.99/1.21      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.21  thf('127', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.99/1.21           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['125', '126'])).
% 0.99/1.21  thf('128', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['11', '12'])).
% 0.99/1.21  thf('129', plain,
% 0.99/1.21      (![X17 : $i, X18 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (k1_xboole_0))),
% 0.99/1.21      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.99/1.21  thf('130', plain,
% 0.99/1.21      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['128', '129'])).
% 0.99/1.21  thf('131', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((k1_xboole_0) = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.99/1.21      inference('demod', [status(thm)], ['127', '130'])).
% 0.99/1.21  thf('132', plain,
% 0.99/1.21      (![X19 : $i, X20 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.99/1.21           = (k3_xboole_0 @ X19 @ X20))),
% 0.99/1.21      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.21  thf('133', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((k4_xboole_0 @ sk_C @ k1_xboole_0)
% 0.99/1.21           = (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['131', '132'])).
% 0.99/1.21  thf(t3_boole, axiom,
% 0.99/1.21    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.99/1.21  thf('134', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.99/1.21      inference('cnf', [status(esa)], [t3_boole])).
% 0.99/1.21  thf('135', plain,
% 0.99/1.21      (![X0 : $i]: ((sk_C) = (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.99/1.21      inference('demod', [status(thm)], ['133', '134'])).
% 0.99/1.21  thf('136', plain,
% 0.99/1.21      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_A) = (sk_C))),
% 0.99/1.21      inference('demod', [status(thm)], ['98', '99', '135'])).
% 0.99/1.21  thf('137', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (sk_B)))),
% 0.99/1.21      inference('demod', [status(thm)], ['68', '77', '78', '79', '136'])).
% 0.99/1.21  thf('138', plain, (((sk_C) = (sk_B))),
% 0.99/1.21      inference('simplify', [status(thm)], ['137'])).
% 0.99/1.21  thf('139', plain, (((sk_C) != (sk_B))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('140', plain, ($false),
% 0.99/1.21      inference('simplify_reflect-', [status(thm)], ['138', '139'])).
% 0.99/1.21  
% 0.99/1.21  % SZS output end Refutation
% 0.99/1.21  
% 0.99/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
