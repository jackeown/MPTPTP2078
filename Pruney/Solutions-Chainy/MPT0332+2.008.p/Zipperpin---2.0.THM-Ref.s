%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1yTslX1GA6

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:08 EST 2020

% Result     : Theorem 1.11s
% Output     : Refutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 602 expanded)
%              Number of leaves         :   24 ( 214 expanded)
%              Depth                    :   28
%              Number of atoms          :  855 (4776 expanded)
%              Number of equality atoms :   93 ( 584 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t145_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t145_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X36 @ X37 )
      | ( r2_hidden @ X38 @ X37 )
      | ( X37
        = ( k4_xboole_0 @ X37 @ ( k2_tarski @ X36 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('2',plain,(
    sk_C
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','20'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','23'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','23'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','47','48'])).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['53','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','23'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','23'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','78'])).

thf('80',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','79'])).

thf('81',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','80'])).

thf('82',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['0','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1yTslX1GA6
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.11/1.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.11/1.32  % Solved by: fo/fo7.sh
% 1.11/1.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.11/1.32  % done 1247 iterations in 0.863s
% 1.11/1.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.11/1.32  % SZS output start Refutation
% 1.11/1.32  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.11/1.32  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.11/1.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.11/1.32  thf(sk_B_type, type, sk_B: $i).
% 1.11/1.32  thf(sk_C_type, type, sk_C: $i).
% 1.11/1.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.11/1.32  thf(sk_A_type, type, sk_A: $i).
% 1.11/1.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.11/1.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.11/1.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.11/1.32  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.11/1.32  thf(t145_zfmisc_1, conjecture,
% 1.11/1.32    (![A:$i,B:$i,C:$i]:
% 1.11/1.32     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.11/1.32          ( ( C ) !=
% 1.11/1.32            ( k4_xboole_0 @
% 1.11/1.32              ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 1.11/1.32              ( k2_tarski @ A @ B ) ) ) ) ))).
% 1.11/1.32  thf(zf_stmt_0, negated_conjecture,
% 1.11/1.32    (~( ![A:$i,B:$i,C:$i]:
% 1.11/1.32        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.11/1.32             ( ( C ) !=
% 1.11/1.32               ( k4_xboole_0 @
% 1.11/1.32                 ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 1.11/1.32                 ( k2_tarski @ A @ B ) ) ) ) ) )),
% 1.11/1.32    inference('cnf.neg', [status(esa)], [t145_zfmisc_1])).
% 1.11/1.32  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf(t144_zfmisc_1, axiom,
% 1.11/1.32    (![A:$i,B:$i,C:$i]:
% 1.11/1.32     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.11/1.32          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 1.11/1.32  thf('1', plain,
% 1.11/1.32      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.11/1.32         ((r2_hidden @ X36 @ X37)
% 1.11/1.32          | (r2_hidden @ X38 @ X37)
% 1.11/1.32          | ((X37) = (k4_xboole_0 @ X37 @ (k2_tarski @ X36 @ X38))))),
% 1.11/1.32      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 1.11/1.32  thf('2', plain,
% 1.11/1.32      (((sk_C)
% 1.11/1.32         != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 1.11/1.32             (k2_tarski @ sk_A @ sk_B)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf(commutativity_k2_xboole_0, axiom,
% 1.11/1.32    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.11/1.32  thf('3', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.11/1.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.11/1.32  thf(t39_xboole_1, axiom,
% 1.11/1.32    (![A:$i,B:$i]:
% 1.11/1.32     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.11/1.32  thf('4', plain,
% 1.11/1.32      (![X10 : $i, X11 : $i]:
% 1.11/1.32         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.11/1.32           = (k2_xboole_0 @ X10 @ X11))),
% 1.11/1.32      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.11/1.32  thf('5', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.11/1.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.11/1.32  thf(t95_xboole_1, axiom,
% 1.11/1.32    (![A:$i,B:$i]:
% 1.11/1.32     ( ( k3_xboole_0 @ A @ B ) =
% 1.11/1.32       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.11/1.32  thf('6', plain,
% 1.11/1.32      (![X16 : $i, X17 : $i]:
% 1.11/1.32         ((k3_xboole_0 @ X16 @ X17)
% 1.11/1.32           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 1.11/1.32              (k2_xboole_0 @ X16 @ X17)))),
% 1.11/1.32      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.11/1.32  thf(t91_xboole_1, axiom,
% 1.11/1.32    (![A:$i,B:$i,C:$i]:
% 1.11/1.32     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.11/1.32       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.11/1.32  thf('7', plain,
% 1.11/1.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.11/1.32           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.11/1.32      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.11/1.32  thf('8', plain,
% 1.11/1.32      (![X16 : $i, X17 : $i]:
% 1.11/1.32         ((k3_xboole_0 @ X16 @ X17)
% 1.11/1.32           = (k5_xboole_0 @ X16 @ 
% 1.11/1.32              (k5_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X17))))),
% 1.11/1.32      inference('demod', [status(thm)], ['6', '7'])).
% 1.11/1.32  thf(commutativity_k5_xboole_0, axiom,
% 1.11/1.32    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.11/1.32  thf('9', plain,
% 1.11/1.32      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.11/1.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.11/1.32  thf(t5_boole, axiom,
% 1.11/1.32    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.11/1.32  thf('10', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.11/1.32      inference('cnf', [status(esa)], [t5_boole])).
% 1.11/1.32  thf('11', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.11/1.32      inference('sup+', [status(thm)], ['9', '10'])).
% 1.11/1.32  thf('12', plain,
% 1.11/1.32      (![X16 : $i, X17 : $i]:
% 1.11/1.32         ((k3_xboole_0 @ X16 @ X17)
% 1.11/1.32           = (k5_xboole_0 @ X16 @ 
% 1.11/1.32              (k5_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X17))))),
% 1.11/1.32      inference('demod', [status(thm)], ['6', '7'])).
% 1.11/1.32  thf('13', plain,
% 1.11/1.32      (![X0 : $i]:
% 1.11/1.32         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 1.11/1.32           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.11/1.32      inference('sup+', [status(thm)], ['11', '12'])).
% 1.11/1.32  thf(t2_boole, axiom,
% 1.11/1.32    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.11/1.32  thf('14', plain,
% 1.11/1.32      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 1.11/1.32      inference('cnf', [status(esa)], [t2_boole])).
% 1.11/1.32  thf(t1_boole, axiom,
% 1.11/1.32    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.11/1.32  thf('15', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 1.11/1.32      inference('cnf', [status(esa)], [t1_boole])).
% 1.11/1.32  thf('16', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.11/1.32      inference('demod', [status(thm)], ['13', '14', '15'])).
% 1.11/1.32  thf('17', plain,
% 1.11/1.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.11/1.32           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.11/1.32      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.11/1.32  thf('18', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.11/1.32           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('sup+', [status(thm)], ['16', '17'])).
% 1.11/1.32  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.11/1.32      inference('sup+', [status(thm)], ['9', '10'])).
% 1.11/1.32  thf('20', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('demod', [status(thm)], ['18', '19'])).
% 1.11/1.32  thf('21', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('sup+', [status(thm)], ['8', '20'])).
% 1.11/1.32  thf(t100_xboole_1, axiom,
% 1.11/1.32    (![A:$i,B:$i]:
% 1.11/1.32     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.11/1.32  thf('22', plain,
% 1.11/1.32      (![X4 : $i, X5 : $i]:
% 1.11/1.32         ((k4_xboole_0 @ X4 @ X5)
% 1.11/1.32           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.11/1.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.11/1.32  thf('23', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k4_xboole_0 @ X1 @ X0))),
% 1.11/1.32      inference('demod', [status(thm)], ['21', '22'])).
% 1.11/1.32  thf('24', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k4_xboole_0 @ X0 @ X1))),
% 1.11/1.32      inference('sup+', [status(thm)], ['5', '23'])).
% 1.11/1.32  thf('25', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 1.11/1.32      inference('sup+', [status(thm)], ['4', '24'])).
% 1.11/1.32  thf('26', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k4_xboole_0 @ X0 @ X1))),
% 1.11/1.32      inference('sup+', [status(thm)], ['5', '23'])).
% 1.11/1.32  thf('27', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.11/1.32           = (k4_xboole_0 @ X1 @ X0))),
% 1.11/1.32      inference('sup+', [status(thm)], ['25', '26'])).
% 1.11/1.32  thf('28', plain,
% 1.11/1.32      (![X4 : $i, X5 : $i]:
% 1.11/1.32         ((k4_xboole_0 @ X4 @ X5)
% 1.11/1.32           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.11/1.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.11/1.32  thf('29', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('demod', [status(thm)], ['18', '19'])).
% 1.11/1.32  thf('30', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k3_xboole_0 @ X1 @ X0)
% 1.11/1.32           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('sup+', [status(thm)], ['28', '29'])).
% 1.11/1.32  thf('31', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.11/1.32           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('sup+', [status(thm)], ['27', '30'])).
% 1.11/1.32  thf('32', plain,
% 1.11/1.32      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.11/1.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.11/1.32  thf('33', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('demod', [status(thm)], ['18', '19'])).
% 1.11/1.32  thf('34', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('sup+', [status(thm)], ['32', '33'])).
% 1.11/1.32  thf('35', plain,
% 1.11/1.32      (![X16 : $i, X17 : $i]:
% 1.11/1.32         ((k3_xboole_0 @ X16 @ X17)
% 1.11/1.32           = (k5_xboole_0 @ X16 @ 
% 1.11/1.32              (k5_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X17))))),
% 1.11/1.32      inference('demod', [status(thm)], ['6', '7'])).
% 1.11/1.32  thf('36', plain,
% 1.11/1.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.11/1.32           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.11/1.32      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.11/1.32  thf('37', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.11/1.32           = (k5_xboole_0 @ X1 @ 
% 1.11/1.32              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ X2)))),
% 1.11/1.32      inference('sup+', [status(thm)], ['35', '36'])).
% 1.11/1.32  thf('38', plain,
% 1.11/1.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.11/1.32           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.11/1.32      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.11/1.32  thf('39', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.11/1.32           = (k5_xboole_0 @ X1 @ 
% 1.11/1.32              (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))))),
% 1.11/1.32      inference('demod', [status(thm)], ['37', '38'])).
% 1.11/1.32  thf('40', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.11/1.32           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('sup+', [status(thm)], ['34', '39'])).
% 1.11/1.32  thf('41', plain,
% 1.11/1.32      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.11/1.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.11/1.32  thf('42', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k4_xboole_0 @ X0 @ X1))),
% 1.11/1.32      inference('sup+', [status(thm)], ['5', '23'])).
% 1.11/1.32  thf('43', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k4_xboole_0 @ X0 @ X1))),
% 1.11/1.32      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.11/1.32  thf('44', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('demod', [status(thm)], ['18', '19'])).
% 1.11/1.32  thf('45', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k3_xboole_0 @ X0 @ X1)
% 1.11/1.32           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('sup+', [status(thm)], ['43', '44'])).
% 1.11/1.32  thf('46', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k3_xboole_0 @ X1 @ X0)
% 1.11/1.32           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('sup+', [status(thm)], ['28', '29'])).
% 1.11/1.32  thf('47', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 1.11/1.32      inference('sup+', [status(thm)], ['45', '46'])).
% 1.11/1.32  thf('48', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.11/1.32      inference('demod', [status(thm)], ['13', '14', '15'])).
% 1.11/1.32  thf('49', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.11/1.32      inference('demod', [status(thm)], ['31', '47', '48'])).
% 1.11/1.32  thf('50', plain,
% 1.11/1.32      (![X4 : $i, X5 : $i]:
% 1.11/1.32         ((k4_xboole_0 @ X4 @ X5)
% 1.11/1.32           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.11/1.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.11/1.32  thf('51', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.11/1.32      inference('sup+', [status(thm)], ['49', '50'])).
% 1.11/1.32  thf('52', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.11/1.32      inference('cnf', [status(esa)], [t5_boole])).
% 1.11/1.32  thf('53', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.11/1.32      inference('demod', [status(thm)], ['51', '52'])).
% 1.11/1.32  thf(t96_xboole_1, axiom,
% 1.11/1.32    (![A:$i,B:$i]:
% 1.11/1.32     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 1.11/1.32  thf('54', plain,
% 1.11/1.32      (![X18 : $i, X19 : $i]:
% 1.11/1.32         (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ (k5_xboole_0 @ X18 @ X19))),
% 1.11/1.32      inference('cnf', [status(esa)], [t96_xboole_1])).
% 1.11/1.32  thf(t12_xboole_1, axiom,
% 1.11/1.32    (![A:$i,B:$i]:
% 1.11/1.32     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.11/1.32  thf('55', plain,
% 1.11/1.32      (![X6 : $i, X7 : $i]:
% 1.11/1.32         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.11/1.32      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.11/1.32  thf('56', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k5_xboole_0 @ X1 @ X0))),
% 1.11/1.32      inference('sup-', [status(thm)], ['54', '55'])).
% 1.11/1.32  thf('57', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k4_xboole_0 @ X1 @ X0))),
% 1.11/1.32      inference('demod', [status(thm)], ['21', '22'])).
% 1.11/1.32  thf('58', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('sup+', [status(thm)], ['56', '57'])).
% 1.11/1.32  thf('59', plain,
% 1.11/1.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.11/1.32           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.11/1.32      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.11/1.32  thf('60', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('sup+', [status(thm)], ['32', '33'])).
% 1.11/1.32  thf('61', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ X1 @ X1)
% 1.11/1.32           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.11/1.32  thf('62', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.11/1.32      inference('demod', [status(thm)], ['13', '14', '15'])).
% 1.11/1.32  thf('63', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k1_xboole_0)
% 1.11/1.32           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('demod', [status(thm)], ['61', '62'])).
% 1.11/1.32  thf('64', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k1_xboole_0)
% 1.11/1.32           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.11/1.32      inference('sup+', [status(thm)], ['53', '63'])).
% 1.11/1.32  thf('65', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k4_xboole_0 @ X0 @ X1))),
% 1.11/1.32      inference('sup+', [status(thm)], ['5', '23'])).
% 1.11/1.32  thf('66', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('demod', [status(thm)], ['18', '19'])).
% 1.11/1.32  thf('67', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k2_xboole_0 @ X0 @ X1)
% 1.11/1.32           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('sup+', [status(thm)], ['65', '66'])).
% 1.11/1.32  thf('68', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.11/1.32      inference('demod', [status(thm)], ['64', '67'])).
% 1.11/1.32  thf('69', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k3_xboole_0 @ X1 @ X0)
% 1.11/1.32           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.11/1.32      inference('sup+', [status(thm)], ['28', '29'])).
% 1.11/1.32  thf('70', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.11/1.32      inference('sup+', [status(thm)], ['68', '69'])).
% 1.11/1.32  thf('71', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.11/1.32      inference('cnf', [status(esa)], [t5_boole])).
% 1.11/1.32  thf('72', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 1.11/1.32      inference('demod', [status(thm)], ['70', '71'])).
% 1.11/1.32  thf('73', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k4_xboole_0 @ X0 @ X1))),
% 1.11/1.32      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.11/1.32  thf('74', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 1.11/1.32           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 1.11/1.32      inference('sup+', [status(thm)], ['72', '73'])).
% 1.11/1.32  thf('75', plain,
% 1.11/1.32      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.11/1.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.11/1.32  thf('76', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 1.11/1.32           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 1.11/1.32      inference('demod', [status(thm)], ['74', '75'])).
% 1.11/1.32  thf('77', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.11/1.32           = (k4_xboole_0 @ X0 @ X1))),
% 1.11/1.32      inference('sup+', [status(thm)], ['5', '23'])).
% 1.11/1.32  thf('78', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 1.11/1.32           = (k4_xboole_0 @ X1 @ X0))),
% 1.11/1.32      inference('sup+', [status(thm)], ['76', '77'])).
% 1.11/1.32  thf('79', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.11/1.32           = (k4_xboole_0 @ X1 @ X0))),
% 1.11/1.32      inference('sup+', [status(thm)], ['3', '78'])).
% 1.11/1.32  thf('80', plain,
% 1.11/1.32      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 1.11/1.32      inference('demod', [status(thm)], ['2', '79'])).
% 1.11/1.32  thf('81', plain,
% 1.11/1.32      ((((sk_C) != (sk_C))
% 1.11/1.32        | (r2_hidden @ sk_B @ sk_C)
% 1.11/1.32        | (r2_hidden @ sk_A @ sk_C))),
% 1.11/1.32      inference('sup-', [status(thm)], ['1', '80'])).
% 1.11/1.32  thf('82', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 1.11/1.32      inference('simplify', [status(thm)], ['81'])).
% 1.11/1.32  thf('83', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('84', plain, ((r2_hidden @ sk_B @ sk_C)),
% 1.11/1.32      inference('clc', [status(thm)], ['82', '83'])).
% 1.11/1.32  thf('85', plain, ($false), inference('demod', [status(thm)], ['0', '84'])).
% 1.11/1.32  
% 1.11/1.32  % SZS output end Refutation
% 1.11/1.32  
% 1.11/1.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
