%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hsXNo8aAFz

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:04 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 540 expanded)
%              Number of leaves         :   20 ( 176 expanded)
%              Depth                    :   25
%              Number of atoms          :  817 (4487 expanded)
%              Number of equality atoms :   69 ( 548 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('21',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('25',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('29',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    = sk_A ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X5 ) )
      | ( r2_hidden @ X2 @ X5 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X5 ) )
      | ( r2_hidden @ X2 @ X5 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['29','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('42',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r2_hidden @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ sk_B @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ sk_A )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(condensation,[status(thm)],['49'])).

thf('51',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('53',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('55',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('60',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','64'])).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_tarski @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','70'])).

thf('72',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('75',plain,
    ( ( k1_xboole_0 = sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('78',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('79',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r2_hidden @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r1_tarski @ ( k2_tarski @ sk_B @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('83',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['7','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hsXNo8aAFz
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:25:14 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.59/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.84  % Solved by: fo/fo7.sh
% 0.59/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.84  % done 839 iterations in 0.392s
% 0.59/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.84  % SZS output start Refutation
% 0.59/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.84  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.84  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.84  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.84  thf(t66_zfmisc_1, conjecture,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.59/0.84          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.59/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.84    (~( ![A:$i,B:$i]:
% 0.59/0.84        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.59/0.84             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.59/0.84    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.59/0.84  thf('0', plain,
% 0.59/0.84      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf(l32_xboole_1, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.84  thf('1', plain,
% 0.59/0.84      (![X9 : $i, X10 : $i]:
% 0.59/0.84         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.59/0.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.84  thf('2', plain,
% 0.59/0.84      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.84        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.84  thf('3', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.59/0.84      inference('simplify', [status(thm)], ['2'])).
% 0.59/0.84  thf(d10_xboole_0, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.84  thf('4', plain,
% 0.59/0.84      (![X6 : $i, X8 : $i]:
% 0.59/0.84         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.59/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.84  thf('5', plain,
% 0.59/0.84      ((~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.59/0.84        | ((k1_tarski @ sk_B) = (sk_A)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.84  thf('6', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('7', plain, (~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.59/0.84      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.59/0.84  thf('8', plain,
% 0.59/0.84      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf(t48_xboole_1, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.84  thf('9', plain,
% 0.59/0.84      (![X15 : $i, X16 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.59/0.84           = (k3_xboole_0 @ X15 @ X16))),
% 0.59/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.84  thf('10', plain,
% 0.59/0.84      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.59/0.84         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['8', '9'])).
% 0.59/0.84  thf(t3_boole, axiom,
% 0.59/0.84    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.84  thf('11', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.59/0.84      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.84  thf('12', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.59/0.84      inference('demod', [status(thm)], ['10', '11'])).
% 0.59/0.84  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.84  thf('13', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.84  thf(t100_xboole_1, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.84  thf('14', plain,
% 0.59/0.84      (![X12 : $i, X13 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X12 @ X13)
% 0.59/0.84           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.59/0.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.84  thf('15', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X0 @ X1)
% 0.59/0.84           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.84  thf('16', plain,
% 0.59/0.84      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.59/0.84         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.59/0.84      inference('sup+', [status(thm)], ['12', '15'])).
% 0.59/0.84  thf('17', plain,
% 0.59/0.84      (![X15 : $i, X16 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.59/0.84           = (k3_xboole_0 @ X15 @ X16))),
% 0.59/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.84  thf('18', plain,
% 0.59/0.84      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.59/0.84         (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))
% 0.59/0.84         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.59/0.84      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.84  thf('19', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.84  thf('20', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.59/0.84      inference('demod', [status(thm)], ['10', '11'])).
% 0.59/0.84  thf('21', plain,
% 0.59/0.84      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.59/0.84         (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)) = (sk_A))),
% 0.59/0.84      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.59/0.84  thf('22', plain,
% 0.59/0.84      (![X15 : $i, X16 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.59/0.84           = (k3_xboole_0 @ X15 @ X16))),
% 0.59/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.84  thf('23', plain,
% 0.59/0.84      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.59/0.84         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.59/0.84            (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.84  thf('24', plain,
% 0.59/0.84      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.59/0.84         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.59/0.84      inference('sup+', [status(thm)], ['12', '15'])).
% 0.59/0.84  thf('25', plain,
% 0.59/0.84      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.59/0.84         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.59/0.84            (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.59/0.84      inference('demod', [status(thm)], ['23', '24'])).
% 0.59/0.84  thf('26', plain,
% 0.59/0.84      (![X12 : $i, X13 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X12 @ X13)
% 0.59/0.84           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.59/0.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.84  thf('27', plain,
% 0.59/0.84      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.59/0.84         (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))
% 0.59/0.84         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.59/0.84            (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['25', '26'])).
% 0.59/0.84  thf('28', plain,
% 0.59/0.84      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.59/0.84         (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)) = (sk_A))),
% 0.59/0.84      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.59/0.84  thf('29', plain,
% 0.59/0.84      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.59/0.84         (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)) = (sk_A))),
% 0.59/0.84      inference('sup+', [status(thm)], ['27', '28'])).
% 0.59/0.84  thf(t69_enumset1, axiom,
% 0.59/0.84    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.84  thf('30', plain,
% 0.59/0.84      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.59/0.84      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.84  thf('31', plain,
% 0.59/0.84      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.59/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.84  thf('32', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.59/0.84      inference('simplify', [status(thm)], ['31'])).
% 0.59/0.84  thf(t38_zfmisc_1, axiom,
% 0.59/0.84    (![A:$i,B:$i,C:$i]:
% 0.59/0.84     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.59/0.84       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.59/0.84  thf('33', plain,
% 0.59/0.84      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.59/0.84         ((r2_hidden @ X23 @ X24)
% 0.59/0.84          | ~ (r1_tarski @ (k2_tarski @ X23 @ X25) @ X24))),
% 0.59/0.84      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.59/0.84  thf('34', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.84  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.59/0.84      inference('sup+', [status(thm)], ['30', '34'])).
% 0.59/0.84  thf(t1_xboole_0, axiom,
% 0.59/0.84    (![A:$i,B:$i,C:$i]:
% 0.59/0.84     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.59/0.84       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.59/0.84  thf('36', plain,
% 0.59/0.84      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.59/0.84         ((r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X5))
% 0.59/0.84          | (r2_hidden @ X2 @ X5)
% 0.59/0.84          | ~ (r2_hidden @ X2 @ X3))),
% 0.59/0.84      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.59/0.84  thf('37', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]:
% 0.59/0.84         ((r2_hidden @ X0 @ X1)
% 0.59/0.84          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.84  thf('38', plain,
% 0.59/0.84      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.59/0.84         ((r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X5))
% 0.59/0.84          | (r2_hidden @ X2 @ X5)
% 0.59/0.84          | ~ (r2_hidden @ X2 @ X3))),
% 0.59/0.84      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.59/0.84  thf('39', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.84         ((r2_hidden @ X1 @ X0)
% 0.59/0.84          | (r2_hidden @ X1 @ X2)
% 0.59/0.84          | (r2_hidden @ X1 @ 
% 0.59/0.84             (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ X1) @ X0) @ X2)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['37', '38'])).
% 0.59/0.84  thf('40', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         ((r2_hidden @ sk_B @ (k5_xboole_0 @ sk_A @ X0))
% 0.59/0.84          | (r2_hidden @ sk_B @ X0)
% 0.59/0.84          | (r2_hidden @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['29', '39'])).
% 0.59/0.84  thf('41', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]:
% 0.59/0.84         ((r2_hidden @ X0 @ X1)
% 0.59/0.84          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.84  thf('42', plain,
% 0.59/0.84      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.59/0.84         ((r1_tarski @ (k2_tarski @ X23 @ X25) @ X26)
% 0.59/0.84          | ~ (r2_hidden @ X25 @ X26)
% 0.59/0.84          | ~ (r2_hidden @ X23 @ X26))),
% 0.59/0.84      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.59/0.84  thf('43', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.84         ((r2_hidden @ X1 @ X0)
% 0.59/0.84          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.59/0.84          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ 
% 0.59/0.84             (k5_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['41', '42'])).
% 0.59/0.84  thf('44', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         ((r2_hidden @ sk_B @ X0)
% 0.59/0.84          | (r2_hidden @ sk_B @ (k5_xboole_0 @ sk_A @ X0))
% 0.59/0.84          | (r1_tarski @ (k2_tarski @ sk_B @ sk_B) @ 
% 0.59/0.84             (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))
% 0.59/0.84          | (r2_hidden @ sk_B @ sk_A))),
% 0.59/0.84      inference('sup-', [status(thm)], ['40', '43'])).
% 0.59/0.84  thf('45', plain,
% 0.59/0.84      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.59/0.84      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.84  thf('46', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         ((r2_hidden @ sk_B @ X0)
% 0.59/0.84          | (r2_hidden @ sk_B @ (k5_xboole_0 @ sk_A @ X0))
% 0.59/0.84          | (r1_tarski @ (k1_tarski @ sk_B) @ 
% 0.59/0.84             (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))
% 0.59/0.84          | (r2_hidden @ sk_B @ sk_A))),
% 0.59/0.84      inference('demod', [status(thm)], ['44', '45'])).
% 0.59/0.84  thf('47', plain,
% 0.59/0.84      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.84         ((r2_hidden @ X2 @ X3)
% 0.59/0.84          | (r2_hidden @ X2 @ X4)
% 0.59/0.84          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X4)))),
% 0.59/0.84      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.59/0.84  thf('48', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         ((r2_hidden @ sk_B @ sk_A)
% 0.59/0.84          | (r1_tarski @ (k1_tarski @ sk_B) @ 
% 0.59/0.84             (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))
% 0.59/0.84          | (r2_hidden @ sk_B @ X0)
% 0.59/0.84          | (r2_hidden @ sk_B @ X0)
% 0.59/0.84          | (r2_hidden @ sk_B @ sk_A))),
% 0.59/0.84      inference('sup-', [status(thm)], ['46', '47'])).
% 0.59/0.84  thf('49', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         ((r2_hidden @ sk_B @ X0)
% 0.59/0.84          | (r1_tarski @ (k1_tarski @ sk_B) @ 
% 0.59/0.84             (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))
% 0.59/0.84          | (r2_hidden @ sk_B @ sk_A))),
% 0.59/0.84      inference('simplify', [status(thm)], ['48'])).
% 0.59/0.84  thf('50', plain,
% 0.59/0.84      (((r2_hidden @ sk_B @ sk_A)
% 0.59/0.84        | (r1_tarski @ (k1_tarski @ sk_B) @ 
% 0.59/0.84           (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.59/0.84      inference('condensation', [status(thm)], ['49'])).
% 0.59/0.84  thf('51', plain,
% 0.59/0.84      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.59/0.84         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.59/0.84            (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.59/0.84      inference('demod', [status(thm)], ['23', '24'])).
% 0.59/0.84  thf('52', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X0 @ X1)
% 0.59/0.84           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.84  thf('53', plain,
% 0.59/0.84      (((k4_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.84         (k1_tarski @ sk_B))
% 0.59/0.84         = (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.84            (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['51', '52'])).
% 0.59/0.84  thf('54', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.59/0.84      inference('simplify', [status(thm)], ['31'])).
% 0.59/0.84  thf('55', plain,
% 0.59/0.84      (![X9 : $i, X11 : $i]:
% 0.59/0.84         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.59/0.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.84  thf('56', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['54', '55'])).
% 0.59/0.84  thf('57', plain,
% 0.59/0.84      (![X15 : $i, X16 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.59/0.84           = (k3_xboole_0 @ X15 @ X16))),
% 0.59/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.84  thf('58', plain,
% 0.59/0.84      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.59/0.84      inference('sup+', [status(thm)], ['56', '57'])).
% 0.59/0.84  thf('59', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.59/0.84      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.84  thf('60', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.59/0.84      inference('demod', [status(thm)], ['58', '59'])).
% 0.59/0.84  thf('61', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X0 @ X1)
% 0.59/0.84           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.84  thf('62', plain,
% 0.59/0.84      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.84      inference('sup+', [status(thm)], ['60', '61'])).
% 0.59/0.84  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['54', '55'])).
% 0.59/0.84  thf('64', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.84      inference('sup+', [status(thm)], ['62', '63'])).
% 0.59/0.84  thf('65', plain,
% 0.59/0.84      (((k4_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.84         (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.59/0.84      inference('demod', [status(thm)], ['53', '64'])).
% 0.59/0.84  thf('66', plain,
% 0.59/0.84      (![X9 : $i, X10 : $i]:
% 0.59/0.84         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.59/0.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.84  thf('67', plain,
% 0.59/0.84      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.84        | (r1_tarski @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.84           (k1_tarski @ sk_B)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['65', '66'])).
% 0.59/0.84  thf('68', plain,
% 0.59/0.84      ((r1_tarski @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.84        (k1_tarski @ sk_B))),
% 0.59/0.84      inference('simplify', [status(thm)], ['67'])).
% 0.59/0.84  thf('69', plain,
% 0.59/0.84      (![X6 : $i, X8 : $i]:
% 0.59/0.84         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.59/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.84  thf('70', plain,
% 0.59/0.84      ((~ (r1_tarski @ (k1_tarski @ sk_B) @ 
% 0.59/0.84           (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))
% 0.59/0.84        | ((k1_tarski @ sk_B) = (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['68', '69'])).
% 0.59/0.84  thf('71', plain,
% 0.59/0.84      (((r2_hidden @ sk_B @ sk_A)
% 0.59/0.84        | ((k1_tarski @ sk_B) = (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['50', '70'])).
% 0.59/0.84  thf('72', plain,
% 0.59/0.84      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.59/0.84         (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)) = (sk_A))),
% 0.59/0.84      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.59/0.84  thf('73', plain,
% 0.59/0.84      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)) = (sk_A))
% 0.59/0.84        | (r2_hidden @ sk_B @ sk_A))),
% 0.59/0.84      inference('sup+', [status(thm)], ['71', '72'])).
% 0.59/0.84  thf('74', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['54', '55'])).
% 0.59/0.84  thf('75', plain, ((((k1_xboole_0) = (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.59/0.84      inference('demod', [status(thm)], ['73', '74'])).
% 0.59/0.84  thf('76', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('77', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.59/0.84      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.59/0.84  thf('78', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.59/0.84      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.59/0.84  thf('79', plain,
% 0.59/0.84      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.59/0.84         ((r1_tarski @ (k2_tarski @ X23 @ X25) @ X26)
% 0.59/0.84          | ~ (r2_hidden @ X25 @ X26)
% 0.59/0.84          | ~ (r2_hidden @ X23 @ X26))),
% 0.59/0.84      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.59/0.84  thf('80', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         (~ (r2_hidden @ X0 @ sk_A)
% 0.59/0.84          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ sk_A))),
% 0.59/0.84      inference('sup-', [status(thm)], ['78', '79'])).
% 0.59/0.84  thf('81', plain, ((r1_tarski @ (k2_tarski @ sk_B @ sk_B) @ sk_A)),
% 0.59/0.84      inference('sup-', [status(thm)], ['77', '80'])).
% 0.59/0.84  thf('82', plain,
% 0.59/0.84      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.59/0.84      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.84  thf('83', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.59/0.84      inference('demod', [status(thm)], ['81', '82'])).
% 0.59/0.84  thf('84', plain, ($false), inference('demod', [status(thm)], ['7', '83'])).
% 0.59/0.84  
% 0.59/0.84  % SZS output end Refutation
% 0.59/0.84  
% 0.59/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
