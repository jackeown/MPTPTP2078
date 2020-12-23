%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.91sTToGZiO

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:00 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 746 expanded)
%              Number of leaves         :   24 ( 254 expanded)
%              Depth                    :   20
%              Number of atoms          : 1302 (6391 expanded)
%              Number of equality atoms :  149 ( 751 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
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
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k2_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_D )
    = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['20','25','28','35'])).

thf('37',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','17','36','47'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('54',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('55',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('57',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_C_1 @ sk_D ) )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_D )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('62',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('64',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('66',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('67',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('69',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('71',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('76',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('78',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('81',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('83',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','17','36','47'])).

thf('84',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('85',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['52','81','82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('87',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('88',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k2_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ X0 )
      = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k2_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('93',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_A ) )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['85','92'])).

thf('94',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('95',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('97',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('99',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('100',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('101',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['98','104'])).

thf('106',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('107',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('109',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('111',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('113',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('114',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('115',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['97','111','112','113','114'])).

thf('116',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('118',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('120',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('122',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('124',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('131',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) )
      = ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k2_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['129','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('139',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('141',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['52','81','82','83','84'])).

thf('143',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['124','143'])).

thf('145',plain,(
    sk_B = sk_C_1 ),
    inference('sup+',[status(thm)],['115','144'])).

thf('146',plain,(
    sk_C_1 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['145','146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.91sTToGZiO
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:59:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 325 iterations in 0.180s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(t72_xboole_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.46/0.65         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.46/0.65       ( ( C ) = ( B ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.46/0.65            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.46/0.65          ( ( C ) = ( B ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(commutativity_k2_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.65  thf(idempotence_k2_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.65  thf('3', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.46/0.65      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.46/0.65  thf(t4_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.65       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X25)
% 0.46/0.65           = (k2_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.65           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['3', '4'])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_C_1 @ sk_D)
% 0.46/0.65         = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['2', '5'])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.46/0.65         = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf(t40_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.46/0.65           = (k4_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.65  thf(t41_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.65       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.46/0.65           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ 
% 0.46/0.65           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1) @ 
% 0.46/0.65           X0) = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['9', '10'])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.46/0.65           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ 
% 0.46/0.65           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1) @ 
% 0.46/0.65           X0) = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B) @ 
% 0.46/0.65         sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_B) @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['8', '13'])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.46/0.65           = (k4_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.65           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.46/0.65         = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.46/0.65           = (k4_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 0.46/0.65         (k2_xboole_0 @ sk_B @ sk_A))
% 0.46/0.65         = (k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['18', '19'])).
% 0.46/0.65  thf(t3_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.65  thf('21', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf(t48_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X21 : $i, X22 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.46/0.65           = (k3_xboole_0 @ X21 @ X22))),
% 0.46/0.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['21', '22'])).
% 0.46/0.65  thf(t2_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.65  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.46/0.65           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.46/0.65           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf('29', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(d7_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.46/0.65       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.46/0.65  thf('31', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.65  thf(t47_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 0.46/0.65           = (k4_xboole_0 @ X19 @ X20))),
% 0.46/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['31', '32'])).
% 0.46/0.65  thf('34', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf('35', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('36', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['20', '25', '28', '35'])).
% 0.46/0.65  thf('37', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.46/0.65           = (k4_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf('40', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['41', '42'])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.46/0.65           = (k4_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['43', '44'])).
% 0.46/0.65  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['14', '17', '36', '47'])).
% 0.46/0.65  thf(t39_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.46/0.65           = (k2_xboole_0 @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.46/0.65           = (k4_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.46/0.65           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['49', '50'])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 0.46/0.65         k1_xboole_0)
% 0.46/0.65         = (k4_xboole_0 @ sk_A @ 
% 0.46/0.65            (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['48', '51'])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.46/0.65           = (k4_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 0.46/0.65         = (k4_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.65      inference('sup+', [status(thm)], ['53', '54'])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.46/0.65           = (k2_xboole_0 @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_C_1 @ sk_D))
% 0.46/0.65         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['55', '56'])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.46/0.65           = (k2_xboole_0 @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_C_1 @ sk_D)
% 0.46/0.65         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.65  thf('62', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.46/0.65         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['60', '61'])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.46/0.65           = (k4_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 0.46/0.65         (k2_xboole_0 @ sk_B @ sk_A))
% 0.46/0.65         = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['62', '63'])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.46/0.65           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.46/0.65           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.65  thf('67', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B) @ 
% 0.46/0.65         sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.46/0.65  thf('68', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.46/0.65           = (k2_xboole_0 @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_A @ 
% 0.46/0.65         (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A))
% 0.46/0.65         = (k2_xboole_0 @ sk_A @ 
% 0.46/0.65            (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['67', '68'])).
% 0.46/0.65  thf('70', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.46/0.65           = (k2_xboole_0 @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.65  thf('71', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B))
% 0.46/0.65         = (k2_xboole_0 @ sk_A @ 
% 0.46/0.65            (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.65  thf('72', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('73', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.46/0.65  thf('74', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['72', '73'])).
% 0.46/0.65  thf('75', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 0.46/0.65           = (k4_xboole_0 @ X19 @ X20))),
% 0.46/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.65  thf('76', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B))),
% 0.46/0.65      inference('sup+', [status(thm)], ['74', '75'])).
% 0.46/0.65  thf('77', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf('78', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['76', '77'])).
% 0.46/0.65  thf('79', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_A @ sk_D)
% 0.46/0.65         = (k2_xboole_0 @ sk_A @ 
% 0.46/0.65            (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['71', '78'])).
% 0.46/0.65  thf('80', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.65           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.65  thf('81', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_A @ sk_D)
% 0.46/0.65         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['79', '80'])).
% 0.46/0.65  thf('82', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf('83', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['14', '17', '36', '47'])).
% 0.46/0.65  thf('84', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf('85', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['52', '81', '82', '83', '84'])).
% 0.46/0.65  thf('86', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('87', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.65  thf('88', plain,
% 0.46/0.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X25)
% 0.46/0.65           = (k2_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.46/0.65  thf('89', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ X0)
% 0.46/0.65           = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_D @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['87', '88'])).
% 0.46/0.65  thf('90', plain,
% 0.46/0.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X25)
% 0.46/0.65           = (k2_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.46/0.65  thf('91', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 0.46/0.65           = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_D @ X0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['89', '90'])).
% 0.46/0.65  thf('92', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 0.46/0.65           = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ X0 @ sk_D)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['86', '91'])).
% 0.46/0.65  thf('93', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_A))
% 0.46/0.65         = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['85', '92'])).
% 0.46/0.65  thf('94', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.46/0.65      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.46/0.65  thf('95', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['93', '94'])).
% 0.46/0.65  thf('96', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.46/0.65           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['49', '50'])).
% 0.46/0.65  thf('97', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 0.46/0.65         (k4_xboole_0 @ sk_A @ sk_C_1))
% 0.46/0.65         = (k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_C_1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['95', '96'])).
% 0.46/0.65  thf('98', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t3_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.46/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.65            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.46/0.65  thf('99', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i]:
% 0.46/0.65         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.65  thf('100', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i]:
% 0.46/0.65         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.65  thf('101', plain,
% 0.46/0.65      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X8 @ X6)
% 0.46/0.65          | ~ (r2_hidden @ X8 @ X9)
% 0.46/0.65          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.65  thf('102', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((r1_xboole_0 @ X1 @ X0)
% 0.46/0.65          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.46/0.65          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['100', '101'])).
% 0.46/0.65  thf('103', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((r1_xboole_0 @ X0 @ X1)
% 0.46/0.65          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.46/0.65          | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['99', '102'])).
% 0.46/0.65  thf('104', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('simplify', [status(thm)], ['103'])).
% 0.46/0.65  thf('105', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.46/0.65      inference('sup-', [status(thm)], ['98', '104'])).
% 0.46/0.65  thf('106', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.46/0.65  thf('107', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['105', '106'])).
% 0.46/0.65  thf('108', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 0.46/0.65           = (k4_xboole_0 @ X19 @ X20))),
% 0.46/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.65  thf('109', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['107', '108'])).
% 0.46/0.65  thf('110', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf('111', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['109', '110'])).
% 0.46/0.65  thf('112', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.46/0.65           = (k4_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.65  thf('113', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['109', '110'])).
% 0.46/0.65  thf('114', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('115', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['97', '111', '112', '113', '114'])).
% 0.46/0.65  thf('116', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('117', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('simplify', [status(thm)], ['103'])).
% 0.46/0.65  thf('118', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.46/0.65      inference('sup-', [status(thm)], ['116', '117'])).
% 0.46/0.65  thf('119', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.46/0.65  thf('120', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['118', '119'])).
% 0.46/0.65  thf('121', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 0.46/0.65           = (k4_xboole_0 @ X19 @ X20))),
% 0.46/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.65  thf('122', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D))),
% 0.46/0.65      inference('sup+', [status(thm)], ['120', '121'])).
% 0.46/0.65  thf('123', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf('124', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['122', '123'])).
% 0.46/0.65  thf('125', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('126', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.46/0.65           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf('127', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1) @ X0)
% 0.46/0.65           = (k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['125', '126'])).
% 0.46/0.65  thf('128', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.46/0.65           = (k4_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.65  thf('129', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['127', '128'])).
% 0.46/0.65  thf('130', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.65  thf('131', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.46/0.65           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.65  thf('132', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D)
% 0.46/0.65           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['130', '131'])).
% 0.46/0.65  thf('133', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.46/0.65           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.65  thf('134', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D)
% 0.46/0.65           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['132', '133'])).
% 0.46/0.65  thf('135', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.46/0.65           = (k2_xboole_0 @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.65  thf('136', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ sk_D @ 
% 0.46/0.65           (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))
% 0.46/0.65           = (k2_xboole_0 @ sk_D @ (k4_xboole_0 @ X0 @ sk_C_1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['134', '135'])).
% 0.46/0.65  thf('137', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_D @ k1_xboole_0)
% 0.46/0.65         = (k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_A @ sk_C_1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['129', '136'])).
% 0.46/0.65  thf('138', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('139', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['109', '110'])).
% 0.46/0.65  thf('140', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('141', plain, (((sk_D) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 0.46/0.65  thf('142', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['52', '81', '82', '83', '84'])).
% 0.46/0.65  thf('143', plain, (((sk_D) = (sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['141', '142'])).
% 0.46/0.65  thf('144', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['124', '143'])).
% 0.46/0.65  thf('145', plain, (((sk_B) = (sk_C_1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['115', '144'])).
% 0.46/0.65  thf('146', plain, (((sk_C_1) != (sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('147', plain, ($false),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['145', '146'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
