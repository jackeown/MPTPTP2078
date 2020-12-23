%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oiVpcKcG2O

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:11 EST 2020

% Result     : Theorem 7.38s
% Output     : Refutation 7.38s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 814 expanded)
%              Number of leaves         :   44 ( 285 expanded)
%              Depth                    :   27
%              Number of atoms          : 1083 (6512 expanded)
%              Number of equality atoms :  113 ( 511 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('16',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','34'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf('45',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('51',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','59'])).

thf('61',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('62',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('63',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('64',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('65',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X50 @ X50 @ X51 @ X52 )
      = ( k1_enumset1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_enumset1 @ X48 @ X48 @ X49 )
      = ( k2_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('68',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i,X66: $i,X67: $i] :
      ( ( k5_enumset1 @ X62 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67 )
      = ( k4_enumset1 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('69',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k4_enumset1 @ X57 @ X57 @ X58 @ X59 @ X60 @ X61 )
      = ( k3_enumset1 @ X57 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k4_enumset1 @ X57 @ X57 @ X58 @ X59 @ X60 @ X61 )
      = ( k3_enumset1 @ X57 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('72',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k5_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 ) @ ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('75',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k3_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56 )
      = ( k2_enumset1 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['67','76'])).

thf('78',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k3_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56 )
      = ( k2_enumset1 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['64','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_tarski @ sk_B_1 @ sk_A )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['63','82'])).

thf('84',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_enumset1 @ X48 @ X48 @ X49 )
      = ( k2_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('85',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 )
      | ( r2_hidden @ X28 @ X32 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('86',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) )
      | ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['84','86'])).

thf('88',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X24 != X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('89',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X25 @ X26 @ X23 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['83','90'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('92',plain,(
    ! [X35: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X38 @ X37 )
      | ( X38 = X35 )
      | ( X37
       != ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('93',plain,(
    ! [X35: $i,X38: $i] :
      ( ( X38 = X35 )
      | ~ ( r2_hidden @ X38 @ ( k1_tarski @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    sk_B_1 = sk_A ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oiVpcKcG2O
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:26:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 7.38/7.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.38/7.56  % Solved by: fo/fo7.sh
% 7.38/7.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.38/7.56  % done 7204 iterations in 7.105s
% 7.38/7.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.38/7.56  % SZS output start Refutation
% 7.38/7.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.38/7.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 7.38/7.56  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 7.38/7.56  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 7.38/7.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.38/7.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.38/7.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 7.38/7.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 7.38/7.56  thf(sk_B_type, type, sk_B: $i > $i).
% 7.38/7.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.38/7.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.38/7.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.38/7.56  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 7.38/7.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.38/7.56  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 7.38/7.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 7.38/7.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.38/7.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 7.38/7.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.38/7.56  thf(sk_A_type, type, sk_A: $i).
% 7.38/7.56  thf(idempotence_k3_xboole_0, axiom,
% 7.38/7.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 7.38/7.56  thf('0', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 7.38/7.56      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 7.38/7.56  thf(t100_xboole_1, axiom,
% 7.38/7.56    (![A:$i,B:$i]:
% 7.38/7.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 7.38/7.56  thf('1', plain,
% 7.38/7.56      (![X9 : $i, X10 : $i]:
% 7.38/7.56         ((k4_xboole_0 @ X9 @ X10)
% 7.38/7.56           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 7.38/7.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.38/7.56  thf('2', plain,
% 7.38/7.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 7.38/7.56      inference('sup+', [status(thm)], ['0', '1'])).
% 7.38/7.56  thf(t36_xboole_1, axiom,
% 7.38/7.56    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 7.38/7.56  thf('3', plain,
% 7.38/7.56      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 7.38/7.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 7.38/7.56  thf(t28_xboole_1, axiom,
% 7.38/7.56    (![A:$i,B:$i]:
% 7.38/7.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 7.38/7.56  thf('4', plain,
% 7.38/7.56      (![X11 : $i, X12 : $i]:
% 7.38/7.56         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 7.38/7.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 7.38/7.56  thf('5', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 7.38/7.56           = (k4_xboole_0 @ X0 @ X1))),
% 7.38/7.56      inference('sup-', [status(thm)], ['3', '4'])).
% 7.38/7.56  thf(commutativity_k3_xboole_0, axiom,
% 7.38/7.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 7.38/7.56  thf('6', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.38/7.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.38/7.56  thf('7', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 7.38/7.56           = (k4_xboole_0 @ X0 @ X1))),
% 7.38/7.56      inference('demod', [status(thm)], ['5', '6'])).
% 7.38/7.56  thf(t79_xboole_1, axiom,
% 7.38/7.56    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 7.38/7.56  thf('8', plain,
% 7.38/7.56      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 7.38/7.56      inference('cnf', [status(esa)], [t79_xboole_1])).
% 7.38/7.56  thf('9', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.38/7.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.38/7.56  thf(t4_xboole_0, axiom,
% 7.38/7.56    (![A:$i,B:$i]:
% 7.38/7.56     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 7.38/7.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 7.38/7.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 7.38/7.56            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 7.38/7.56  thf('10', plain,
% 7.38/7.56      (![X4 : $i, X5 : $i]:
% 7.38/7.56         ((r1_xboole_0 @ X4 @ X5)
% 7.38/7.56          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 7.38/7.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 7.38/7.56  thf('11', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 7.38/7.56          | (r1_xboole_0 @ X0 @ X1))),
% 7.38/7.56      inference('sup+', [status(thm)], ['9', '10'])).
% 7.38/7.56  thf('12', plain,
% 7.38/7.56      (![X4 : $i, X6 : $i, X7 : $i]:
% 7.38/7.56         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 7.38/7.56          | ~ (r1_xboole_0 @ X4 @ X7))),
% 7.38/7.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 7.38/7.56  thf('13', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 7.38/7.56      inference('sup-', [status(thm)], ['11', '12'])).
% 7.38/7.56  thf('14', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 7.38/7.56      inference('sup-', [status(thm)], ['8', '13'])).
% 7.38/7.56  thf(t7_xboole_0, axiom,
% 7.38/7.56    (![A:$i]:
% 7.38/7.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 7.38/7.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 7.38/7.56  thf('15', plain,
% 7.38/7.56      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 7.38/7.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 7.38/7.56  thf('16', plain,
% 7.38/7.56      (![X4 : $i, X6 : $i, X7 : $i]:
% 7.38/7.56         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 7.38/7.56          | ~ (r1_xboole_0 @ X4 @ X7))),
% 7.38/7.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 7.38/7.56  thf('17', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 7.38/7.56      inference('sup-', [status(thm)], ['15', '16'])).
% 7.38/7.56  thf('18', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 7.38/7.56      inference('sup-', [status(thm)], ['14', '17'])).
% 7.38/7.56  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 7.38/7.56      inference('sup+', [status(thm)], ['7', '18'])).
% 7.38/7.56  thf('20', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 7.38/7.56      inference('demod', [status(thm)], ['2', '19'])).
% 7.38/7.56  thf(t13_zfmisc_1, conjecture,
% 7.38/7.56    (![A:$i,B:$i]:
% 7.38/7.56     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 7.38/7.56         ( k1_tarski @ A ) ) =>
% 7.38/7.56       ( ( A ) = ( B ) ) ))).
% 7.38/7.56  thf(zf_stmt_0, negated_conjecture,
% 7.38/7.56    (~( ![A:$i,B:$i]:
% 7.38/7.56        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 7.38/7.56            ( k1_tarski @ A ) ) =>
% 7.38/7.56          ( ( A ) = ( B ) ) ) )),
% 7.38/7.56    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 7.38/7.56  thf('21', plain,
% 7.38/7.56      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 7.38/7.56         = (k1_tarski @ sk_A))),
% 7.38/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.38/7.56  thf(t98_xboole_1, axiom,
% 7.38/7.56    (![A:$i,B:$i]:
% 7.38/7.56     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 7.38/7.56  thf('22', plain,
% 7.38/7.56      (![X21 : $i, X22 : $i]:
% 7.38/7.56         ((k2_xboole_0 @ X21 @ X22)
% 7.38/7.56           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 7.38/7.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 7.38/7.56  thf('23', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 7.38/7.56      inference('demod', [status(thm)], ['2', '19'])).
% 7.38/7.56  thf(t91_xboole_1, axiom,
% 7.38/7.56    (![A:$i,B:$i,C:$i]:
% 7.38/7.56     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 7.38/7.56       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 7.38/7.56  thf('24', plain,
% 7.38/7.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.38/7.56         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 7.38/7.56           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 7.38/7.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 7.38/7.56  thf('25', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 7.38/7.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 7.38/7.56      inference('sup+', [status(thm)], ['23', '24'])).
% 7.38/7.56  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 7.38/7.56      inference('sup+', [status(thm)], ['7', '18'])).
% 7.38/7.56  thf('27', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 7.38/7.56      inference('sup-', [status(thm)], ['14', '17'])).
% 7.38/7.56  thf('28', plain,
% 7.38/7.56      (![X9 : $i, X10 : $i]:
% 7.38/7.56         ((k4_xboole_0 @ X9 @ X10)
% 7.38/7.56           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 7.38/7.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.38/7.56  thf('29', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 7.38/7.56           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 7.38/7.56      inference('sup+', [status(thm)], ['27', '28'])).
% 7.38/7.56  thf(t5_boole, axiom,
% 7.38/7.56    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 7.38/7.56  thf('30', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 7.38/7.56      inference('cnf', [status(esa)], [t5_boole])).
% 7.38/7.56  thf('31', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 7.38/7.56      inference('demod', [status(thm)], ['29', '30'])).
% 7.38/7.56  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 7.38/7.56      inference('sup+', [status(thm)], ['26', '31'])).
% 7.38/7.56  thf('33', plain,
% 7.38/7.56      (![X21 : $i, X22 : $i]:
% 7.38/7.56         ((k2_xboole_0 @ X21 @ X22)
% 7.38/7.56           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 7.38/7.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 7.38/7.56  thf('34', plain,
% 7.38/7.56      (![X0 : $i]:
% 7.38/7.56         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 7.38/7.56      inference('sup+', [status(thm)], ['32', '33'])).
% 7.38/7.56  thf('35', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 7.38/7.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 7.38/7.56      inference('demod', [status(thm)], ['25', '34'])).
% 7.38/7.56  thf('36', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 7.38/7.56      inference('demod', [status(thm)], ['2', '19'])).
% 7.38/7.56  thf('37', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 7.38/7.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 7.38/7.56      inference('demod', [status(thm)], ['25', '34'])).
% 7.38/7.56  thf('38', plain,
% 7.38/7.56      (![X0 : $i]:
% 7.38/7.56         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 7.38/7.56      inference('sup+', [status(thm)], ['36', '37'])).
% 7.38/7.56  thf('39', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 7.38/7.56      inference('cnf', [status(esa)], [t5_boole])).
% 7.38/7.56  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 7.38/7.56      inference('sup+', [status(thm)], ['38', '39'])).
% 7.38/7.56  thf('41', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 7.38/7.56      inference('demod', [status(thm)], ['35', '40'])).
% 7.38/7.56  thf('42', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k4_xboole_0 @ X0 @ X1)
% 7.38/7.56           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 7.38/7.56      inference('sup+', [status(thm)], ['22', '41'])).
% 7.38/7.56  thf('43', plain,
% 7.38/7.56      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 7.38/7.56         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 7.38/7.56      inference('sup+', [status(thm)], ['21', '42'])).
% 7.38/7.56  thf('44', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 7.38/7.56      inference('demod', [status(thm)], ['2', '19'])).
% 7.38/7.56  thf('45', plain,
% 7.38/7.56      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 7.38/7.56         = (k1_xboole_0))),
% 7.38/7.56      inference('demod', [status(thm)], ['43', '44'])).
% 7.38/7.56  thf('46', plain,
% 7.38/7.56      (![X9 : $i, X10 : $i]:
% 7.38/7.56         ((k4_xboole_0 @ X9 @ X10)
% 7.38/7.56           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 7.38/7.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.38/7.56  thf('47', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 7.38/7.56      inference('demod', [status(thm)], ['35', '40'])).
% 7.38/7.56  thf('48', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k3_xboole_0 @ X1 @ X0)
% 7.38/7.56           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 7.38/7.56      inference('sup+', [status(thm)], ['46', '47'])).
% 7.38/7.56  thf('49', plain,
% 7.38/7.56      (((k3_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 7.38/7.56         = (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0))),
% 7.38/7.56      inference('sup+', [status(thm)], ['45', '48'])).
% 7.38/7.56  thf('50', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 7.38/7.56      inference('cnf', [status(esa)], [t5_boole])).
% 7.38/7.56  thf('51', plain,
% 7.38/7.56      (((k3_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 7.38/7.56         = (k1_tarski @ sk_B_1))),
% 7.38/7.56      inference('demod', [status(thm)], ['49', '50'])).
% 7.38/7.56  thf('52', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.38/7.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.38/7.56  thf('53', plain,
% 7.38/7.56      (![X9 : $i, X10 : $i]:
% 7.38/7.56         ((k4_xboole_0 @ X9 @ X10)
% 7.38/7.56           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 7.38/7.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.38/7.56  thf('54', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k4_xboole_0 @ X0 @ X1)
% 7.38/7.56           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 7.38/7.56      inference('sup+', [status(thm)], ['52', '53'])).
% 7.38/7.56  thf('55', plain,
% 7.38/7.56      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 7.38/7.56         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))),
% 7.38/7.56      inference('sup+', [status(thm)], ['51', '54'])).
% 7.38/7.56  thf('56', plain,
% 7.38/7.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.38/7.56         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 7.38/7.56           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 7.38/7.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 7.38/7.56  thf('57', plain,
% 7.38/7.56      (![X0 : $i]:
% 7.38/7.56         ((k5_xboole_0 @ 
% 7.38/7.56           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)) @ X0)
% 7.38/7.56           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 7.38/7.56              (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ X0)))),
% 7.38/7.56      inference('sup+', [status(thm)], ['55', '56'])).
% 7.38/7.56  thf('58', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 7.38/7.56      inference('demod', [status(thm)], ['35', '40'])).
% 7.38/7.56  thf('59', plain,
% 7.38/7.56      (![X0 : $i]:
% 7.38/7.56         ((k5_xboole_0 @ (k1_tarski @ sk_B_1) @ X0)
% 7.38/7.56           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 7.38/7.56              (k5_xboole_0 @ 
% 7.38/7.56               (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)) @ X0)))),
% 7.38/7.56      inference('sup+', [status(thm)], ['57', '58'])).
% 7.38/7.56  thf('60', plain,
% 7.38/7.56      (((k5_xboole_0 @ (k1_tarski @ sk_B_1) @ 
% 7.38/7.56         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))
% 7.38/7.56         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 7.38/7.56      inference('sup+', [status(thm)], ['20', '59'])).
% 7.38/7.56  thf('61', plain,
% 7.38/7.56      (![X21 : $i, X22 : $i]:
% 7.38/7.56         ((k2_xboole_0 @ X21 @ X22)
% 7.38/7.56           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 7.38/7.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 7.38/7.56  thf('62', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 7.38/7.56      inference('cnf', [status(esa)], [t5_boole])).
% 7.38/7.56  thf('63', plain,
% 7.38/7.56      (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 7.38/7.56         = (k1_tarski @ sk_A))),
% 7.38/7.56      inference('demod', [status(thm)], ['60', '61', '62'])).
% 7.38/7.56  thf(t69_enumset1, axiom,
% 7.38/7.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 7.38/7.56  thf('64', plain,
% 7.38/7.56      (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 7.38/7.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.38/7.56  thf(t71_enumset1, axiom,
% 7.38/7.56    (![A:$i,B:$i,C:$i]:
% 7.38/7.56     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 7.38/7.56  thf('65', plain,
% 7.38/7.56      (![X50 : $i, X51 : $i, X52 : $i]:
% 7.38/7.56         ((k2_enumset1 @ X50 @ X50 @ X51 @ X52)
% 7.38/7.56           = (k1_enumset1 @ X50 @ X51 @ X52))),
% 7.38/7.56      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.38/7.56  thf(t70_enumset1, axiom,
% 7.38/7.56    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 7.38/7.56  thf('66', plain,
% 7.38/7.56      (![X48 : $i, X49 : $i]:
% 7.38/7.56         ((k1_enumset1 @ X48 @ X48 @ X49) = (k2_tarski @ X48 @ X49))),
% 7.38/7.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.38/7.56  thf('67', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 7.38/7.56      inference('sup+', [status(thm)], ['65', '66'])).
% 7.38/7.56  thf(t74_enumset1, axiom,
% 7.38/7.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 7.38/7.56     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 7.38/7.56       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 7.38/7.56  thf('68', plain,
% 7.38/7.56      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i, X67 : $i]:
% 7.38/7.56         ((k5_enumset1 @ X62 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67)
% 7.38/7.56           = (k4_enumset1 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67))),
% 7.38/7.56      inference('cnf', [status(esa)], [t74_enumset1])).
% 7.38/7.56  thf(t73_enumset1, axiom,
% 7.38/7.56    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 7.38/7.56     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 7.38/7.56       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 7.38/7.56  thf('69', plain,
% 7.38/7.56      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 7.38/7.56         ((k4_enumset1 @ X57 @ X57 @ X58 @ X59 @ X60 @ X61)
% 7.38/7.56           = (k3_enumset1 @ X57 @ X58 @ X59 @ X60 @ X61))),
% 7.38/7.56      inference('cnf', [status(esa)], [t73_enumset1])).
% 7.38/7.56  thf('70', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 7.38/7.56         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 7.38/7.56           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 7.38/7.56      inference('sup+', [status(thm)], ['68', '69'])).
% 7.38/7.56  thf('71', plain,
% 7.38/7.56      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 7.38/7.56         ((k4_enumset1 @ X57 @ X57 @ X58 @ X59 @ X60 @ X61)
% 7.38/7.56           = (k3_enumset1 @ X57 @ X58 @ X59 @ X60 @ X61))),
% 7.38/7.56      inference('cnf', [status(esa)], [t73_enumset1])).
% 7.38/7.56  thf(t61_enumset1, axiom,
% 7.38/7.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 7.38/7.56     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 7.38/7.56       ( k2_xboole_0 @
% 7.38/7.56         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 7.38/7.56  thf('72', plain,
% 7.38/7.56      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 7.38/7.56         ((k5_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 7.38/7.56           = (k2_xboole_0 @ 
% 7.38/7.56              (k4_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45) @ 
% 7.38/7.56              (k1_tarski @ X46)))),
% 7.38/7.56      inference('cnf', [status(esa)], [t61_enumset1])).
% 7.38/7.56  thf('73', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 7.38/7.56         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 7.38/7.56           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 7.38/7.56              (k1_tarski @ X5)))),
% 7.38/7.56      inference('sup+', [status(thm)], ['71', '72'])).
% 7.38/7.56  thf('74', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 7.38/7.56         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 7.38/7.56           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 7.38/7.56              (k1_tarski @ X0)))),
% 7.38/7.56      inference('sup+', [status(thm)], ['70', '73'])).
% 7.38/7.56  thf(t72_enumset1, axiom,
% 7.38/7.56    (![A:$i,B:$i,C:$i,D:$i]:
% 7.38/7.56     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 7.38/7.56  thf('75', plain,
% 7.38/7.56      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 7.38/7.56         ((k3_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56)
% 7.38/7.56           = (k2_enumset1 @ X53 @ X54 @ X55 @ X56))),
% 7.38/7.56      inference('cnf', [status(esa)], [t72_enumset1])).
% 7.38/7.56  thf('76', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 7.38/7.56         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 7.38/7.56           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 7.38/7.56              (k1_tarski @ X0)))),
% 7.38/7.56      inference('demod', [status(thm)], ['74', '75'])).
% 7.38/7.56  thf('77', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.38/7.56         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 7.38/7.56           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 7.38/7.56      inference('sup+', [status(thm)], ['67', '76'])).
% 7.38/7.56  thf('78', plain,
% 7.38/7.56      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 7.38/7.56         ((k3_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56)
% 7.38/7.56           = (k2_enumset1 @ X53 @ X54 @ X55 @ X56))),
% 7.38/7.56      inference('cnf', [status(esa)], [t72_enumset1])).
% 7.38/7.56  thf('79', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.38/7.56         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 7.38/7.56           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 7.38/7.56      inference('demod', [status(thm)], ['77', '78'])).
% 7.38/7.56  thf('80', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 7.38/7.56           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 7.38/7.56      inference('sup+', [status(thm)], ['64', '79'])).
% 7.38/7.56  thf('81', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 7.38/7.56      inference('sup+', [status(thm)], ['65', '66'])).
% 7.38/7.56  thf('82', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]:
% 7.38/7.56         ((k2_tarski @ X0 @ X1)
% 7.38/7.56           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 7.38/7.56      inference('demod', [status(thm)], ['80', '81'])).
% 7.38/7.56  thf('83', plain, (((k2_tarski @ sk_B_1 @ sk_A) = (k1_tarski @ sk_A))),
% 7.38/7.56      inference('demod', [status(thm)], ['63', '82'])).
% 7.38/7.56  thf('84', plain,
% 7.38/7.56      (![X48 : $i, X49 : $i]:
% 7.38/7.56         ((k1_enumset1 @ X48 @ X48 @ X49) = (k2_tarski @ X48 @ X49))),
% 7.38/7.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.38/7.56  thf(d1_enumset1, axiom,
% 7.38/7.56    (![A:$i,B:$i,C:$i,D:$i]:
% 7.38/7.56     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 7.38/7.56       ( ![E:$i]:
% 7.38/7.56         ( ( r2_hidden @ E @ D ) <=>
% 7.38/7.56           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 7.38/7.56  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 7.38/7.56  thf(zf_stmt_2, axiom,
% 7.38/7.56    (![E:$i,C:$i,B:$i,A:$i]:
% 7.38/7.56     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 7.38/7.56       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 7.38/7.56  thf(zf_stmt_3, axiom,
% 7.38/7.56    (![A:$i,B:$i,C:$i,D:$i]:
% 7.38/7.56     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 7.38/7.56       ( ![E:$i]:
% 7.38/7.56         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 7.38/7.56  thf('85', plain,
% 7.38/7.56      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 7.38/7.56         ((zip_tseitin_0 @ X28 @ X29 @ X30 @ X31)
% 7.38/7.56          | (r2_hidden @ X28 @ X32)
% 7.38/7.56          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 7.38/7.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.38/7.56  thf('86', plain,
% 7.38/7.56      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 7.38/7.56         ((r2_hidden @ X28 @ (k1_enumset1 @ X31 @ X30 @ X29))
% 7.38/7.56          | (zip_tseitin_0 @ X28 @ X29 @ X30 @ X31))),
% 7.38/7.56      inference('simplify', [status(thm)], ['85'])).
% 7.38/7.56  thf('87', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.38/7.56         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 7.38/7.56          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 7.38/7.56      inference('sup+', [status(thm)], ['84', '86'])).
% 7.38/7.56  thf('88', plain,
% 7.38/7.56      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 7.38/7.56         (((X24) != (X23)) | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 7.38/7.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.38/7.56  thf('89', plain,
% 7.38/7.56      (![X23 : $i, X25 : $i, X26 : $i]:
% 7.38/7.56         ~ (zip_tseitin_0 @ X23 @ X25 @ X26 @ X23)),
% 7.38/7.56      inference('simplify', [status(thm)], ['88'])).
% 7.38/7.56  thf('90', plain,
% 7.38/7.56      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 7.38/7.56      inference('sup-', [status(thm)], ['87', '89'])).
% 7.38/7.56  thf('91', plain, ((r2_hidden @ sk_B_1 @ (k1_tarski @ sk_A))),
% 7.38/7.56      inference('sup+', [status(thm)], ['83', '90'])).
% 7.38/7.56  thf(d1_tarski, axiom,
% 7.38/7.56    (![A:$i,B:$i]:
% 7.38/7.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 7.38/7.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 7.38/7.56  thf('92', plain,
% 7.38/7.56      (![X35 : $i, X37 : $i, X38 : $i]:
% 7.38/7.56         (~ (r2_hidden @ X38 @ X37)
% 7.38/7.56          | ((X38) = (X35))
% 7.38/7.56          | ((X37) != (k1_tarski @ X35)))),
% 7.38/7.56      inference('cnf', [status(esa)], [d1_tarski])).
% 7.38/7.56  thf('93', plain,
% 7.38/7.56      (![X35 : $i, X38 : $i]:
% 7.38/7.56         (((X38) = (X35)) | ~ (r2_hidden @ X38 @ (k1_tarski @ X35)))),
% 7.38/7.56      inference('simplify', [status(thm)], ['92'])).
% 7.38/7.56  thf('94', plain, (((sk_B_1) = (sk_A))),
% 7.38/7.56      inference('sup-', [status(thm)], ['91', '93'])).
% 7.38/7.56  thf('95', plain, (((sk_A) != (sk_B_1))),
% 7.38/7.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.38/7.56  thf('96', plain, ($false),
% 7.38/7.56      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 7.38/7.56  
% 7.38/7.56  % SZS output end Refutation
% 7.38/7.56  
% 7.38/7.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
