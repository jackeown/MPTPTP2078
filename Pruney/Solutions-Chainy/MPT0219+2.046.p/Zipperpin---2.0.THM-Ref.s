%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.70Q5SoY63H

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:09 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  183 (2368 expanded)
%              Number of leaves         :   24 ( 758 expanded)
%              Depth                    :   43
%              Number of atoms          : 1728 (18669 expanded)
%              Number of equality atoms :  121 (1259 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

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

thf('15',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('33',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('44',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','45'])).

thf('47',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('50',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) @ X0 )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) @ ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['14','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('64',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) @ X0 )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ) @ ( k1_tarski @ sk_A ) )
      | ( r1_tarski @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','70'])).

thf('72',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('73',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ) @ ( k1_tarski @ sk_A ) )
      | ( r1_tarski @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ) @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ) @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('77',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('80',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('83',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79','80','81','82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','84'])).

thf('86',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) )
      | ( r1_tarski @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) @ X0 ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      | ( r1_tarski @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['59','66'])).

thf('92',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['59','66'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['59','66'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['59','66'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93','94','95','96','97','98','99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['5','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('105',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('106',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) @ k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','35'])).

thf('110',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['31','34'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['121','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['120','127'])).

thf('129',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['119','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('131',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('133',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['131','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('137',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['121','126'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['121','126'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['135','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['121','126'])).

thf('149',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('151',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('153',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('154',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38 = X37 )
      | ~ ( r1_tarski @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('155',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['155','156'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.70Q5SoY63H
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.81/1.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.81/1.02  % Solved by: fo/fo7.sh
% 0.81/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.02  % done 896 iterations in 0.567s
% 0.81/1.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.81/1.02  % SZS output start Refutation
% 0.81/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.81/1.02  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.81/1.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.81/1.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.81/1.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.81/1.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.81/1.02  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.81/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.02  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.81/1.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.81/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.81/1.02  thf(d10_xboole_0, axiom,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.81/1.02  thf('0', plain,
% 0.81/1.02      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 0.81/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.02  thf('1', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.81/1.02      inference('simplify', [status(thm)], ['0'])).
% 0.81/1.02  thf(t28_xboole_1, axiom,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.81/1.02  thf('2', plain,
% 0.81/1.02      (![X17 : $i, X18 : $i]:
% 0.81/1.02         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.81/1.02      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.81/1.02  thf('3', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['1', '2'])).
% 0.81/1.02  thf(t100_xboole_1, axiom,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.81/1.02  thf('4', plain,
% 0.81/1.02      (![X14 : $i, X15 : $i]:
% 0.81/1.02         ((k4_xboole_0 @ X14 @ X15)
% 0.81/1.02           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.81/1.02  thf('5', plain,
% 0.81/1.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['3', '4'])).
% 0.81/1.02  thf('6', plain,
% 0.81/1.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['3', '4'])).
% 0.81/1.02  thf(t91_xboole_1, axiom,
% 0.81/1.02    (![A:$i,B:$i,C:$i]:
% 0.81/1.02     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.81/1.02       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.81/1.02  thf('7', plain,
% 0.81/1.02      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.81/1.02           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.81/1.02  thf('8', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.81/1.02           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['6', '7'])).
% 0.81/1.02  thf(d3_tarski, axiom,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( r1_tarski @ A @ B ) <=>
% 0.81/1.02       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.81/1.02  thf('9', plain,
% 0.81/1.02      (![X3 : $i, X5 : $i]:
% 0.81/1.02         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.81/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.81/1.02  thf(t1_xboole_0, axiom,
% 0.81/1.02    (![A:$i,B:$i,C:$i]:
% 0.81/1.02     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.81/1.02       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.81/1.02  thf('10', plain,
% 0.81/1.02      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.81/1.02         ((r2_hidden @ X7 @ X8)
% 0.81/1.02          | (r2_hidden @ X7 @ X9)
% 0.81/1.02          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.81/1.02  thf('11', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         ((r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.81/1.02          | (r2_hidden @ (sk_C @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ X0)
% 0.81/1.02          | (r2_hidden @ (sk_C @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ X1))),
% 0.81/1.02      inference('sup-', [status(thm)], ['9', '10'])).
% 0.81/1.02  thf('12', plain,
% 0.81/1.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['3', '4'])).
% 0.81/1.02  thf('13', plain,
% 0.81/1.02      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.81/1.02           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.81/1.02  thf('14', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         ((r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.81/1.02          | (r2_hidden @ (sk_C @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ X0)
% 0.81/1.02          | (r2_hidden @ (sk_C @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ X1))),
% 0.81/1.02      inference('sup-', [status(thm)], ['9', '10'])).
% 0.81/1.02  thf(t13_zfmisc_1, conjecture,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.81/1.02         ( k1_tarski @ A ) ) =>
% 0.81/1.02       ( ( A ) = ( B ) ) ))).
% 0.81/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.81/1.02    (~( ![A:$i,B:$i]:
% 0.81/1.02        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.81/1.02            ( k1_tarski @ A ) ) =>
% 0.81/1.02          ( ( A ) = ( B ) ) ) )),
% 0.81/1.02    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.81/1.02  thf('15', plain,
% 0.81/1.02      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.81/1.02         = (k1_tarski @ sk_A))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf(t98_xboole_1, axiom,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.81/1.02  thf('16', plain,
% 0.81/1.02      (![X25 : $i, X26 : $i]:
% 0.81/1.02         ((k2_xboole_0 @ X25 @ X26)
% 0.81/1.02           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.81/1.02  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.81/1.02  thf('17', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 0.81/1.02      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.81/1.02  thf('18', plain,
% 0.81/1.02      (![X17 : $i, X18 : $i]:
% 0.81/1.02         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.81/1.02      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.81/1.02  thf('19', plain,
% 0.81/1.02      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['17', '18'])).
% 0.81/1.02  thf(commutativity_k3_xboole_0, axiom,
% 0.81/1.02    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.81/1.02  thf('20', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.81/1.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.81/1.02  thf('21', plain,
% 0.81/1.02      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['19', '20'])).
% 0.81/1.02  thf('22', plain,
% 0.81/1.02      (![X14 : $i, X15 : $i]:
% 0.81/1.02         ((k4_xboole_0 @ X14 @ X15)
% 0.81/1.02           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.81/1.02  thf('23', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['21', '22'])).
% 0.81/1.02  thf('24', plain,
% 0.81/1.02      (![X3 : $i, X5 : $i]:
% 0.81/1.02         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.81/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.81/1.02  thf('25', plain,
% 0.81/1.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['3', '4'])).
% 0.81/1.02  thf('26', plain,
% 0.81/1.02      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.81/1.02         ((r2_hidden @ X7 @ X8)
% 0.81/1.02          | (r2_hidden @ X7 @ X9)
% 0.81/1.02          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.81/1.02  thf('27', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.81/1.02          | (r2_hidden @ X1 @ X0)
% 0.81/1.02          | (r2_hidden @ X1 @ X0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['25', '26'])).
% 0.81/1.02  thf('28', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.81/1.02      inference('simplify', [status(thm)], ['27'])).
% 0.81/1.02  thf('29', plain,
% 0.81/1.02      (![X25 : $i, X26 : $i]:
% 0.81/1.02         ((k2_xboole_0 @ X25 @ X26)
% 0.81/1.02           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.81/1.02  thf('30', plain,
% 0.81/1.02      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X7 @ X8)
% 0.81/1.02          | ~ (r2_hidden @ X7 @ X9)
% 0.81/1.02          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.81/1.02  thf('31', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.81/1.02          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.81/1.02          | ~ (r2_hidden @ X2 @ X1))),
% 0.81/1.02      inference('sup-', [status(thm)], ['29', '30'])).
% 0.81/1.02  thf(t7_xboole_1, axiom,
% 0.81/1.02    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.81/1.02  thf('32', plain,
% 0.81/1.02      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.81/1.02      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.81/1.02  thf('33', plain,
% 0.81/1.02      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X2 @ X3)
% 0.81/1.02          | (r2_hidden @ X2 @ X4)
% 0.81/1.02          | ~ (r1_tarski @ X3 @ X4))),
% 0.81/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.81/1.02  thf('34', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.81/1.02      inference('sup-', [status(thm)], ['32', '33'])).
% 0.81/1.02  thf('35', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X2 @ X1)
% 0.81/1.02          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.81/1.02      inference('clc', [status(thm)], ['31', '34'])).
% 0.81/1.02  thf('36', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.81/1.02      inference('clc', [status(thm)], ['28', '35'])).
% 0.81/1.02  thf('37', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.81/1.02      inference('sup-', [status(thm)], ['24', '36'])).
% 0.81/1.02  thf('38', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 0.81/1.02      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.81/1.02  thf('39', plain,
% 0.81/1.02      (![X11 : $i, X13 : $i]:
% 0.81/1.02         (((X11) = (X13))
% 0.81/1.02          | ~ (r1_tarski @ X13 @ X11)
% 0.81/1.02          | ~ (r1_tarski @ X11 @ X13))),
% 0.81/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.02  thf('40', plain,
% 0.81/1.02      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['38', '39'])).
% 0.81/1.02  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('42', plain,
% 0.81/1.02      (![X25 : $i, X26 : $i]:
% 0.81/1.02         ((k2_xboole_0 @ X25 @ X26)
% 0.81/1.02           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.81/1.02  thf('43', plain,
% 0.81/1.02      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['41', '42'])).
% 0.81/1.02  thf(idempotence_k2_xboole_0, axiom,
% 0.81/1.02    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.81/1.02  thf('44', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.81/1.02      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.81/1.02  thf('45', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.02      inference('demod', [status(thm)], ['43', '44'])).
% 0.81/1.02  thf('46', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['23', '45'])).
% 0.81/1.02  thf('47', plain,
% 0.81/1.02      (![X25 : $i, X26 : $i]:
% 0.81/1.02         ((k2_xboole_0 @ X25 @ X26)
% 0.81/1.02           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.81/1.02  thf('48', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['46', '47'])).
% 0.81/1.02  thf('49', plain,
% 0.81/1.02      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.81/1.02           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.81/1.02  thf('50', plain,
% 0.81/1.02      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X7 @ X8)
% 0.81/1.02          | ~ (r2_hidden @ X7 @ X9)
% 0.81/1.02          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.81/1.02  thf('51', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))
% 0.81/1.02          | ~ (r2_hidden @ X3 @ X0)
% 0.81/1.02          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ X1)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['49', '50'])).
% 0.81/1.02  thf('52', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X2 @ 
% 0.81/1.02             (k2_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.81/1.02          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ k1_xboole_0 @ X1))
% 0.81/1.02          | ~ (r2_hidden @ X2 @ X0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['48', '51'])).
% 0.81/1.02  thf('53', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['46', '47'])).
% 0.81/1.02  thf('54', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X2 @ 
% 0.81/1.02             (k2_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.81/1.02          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ k1_xboole_0 @ X1))
% 0.81/1.02          | ~ (r2_hidden @ X2 @ X0))),
% 0.81/1.02      inference('demod', [status(thm)], ['52', '53'])).
% 0.81/1.02  thf('55', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X2 @ 
% 0.81/1.02             (k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)))
% 0.81/1.02          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.81/1.02          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['16', '54'])).
% 0.81/1.02  thf('56', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)))
% 0.81/1.02          | ~ (r2_hidden @ X0 @ 
% 0.81/1.02               (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)))
% 0.81/1.02          | ~ (r2_hidden @ X0 @ 
% 0.81/1.02               (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))),
% 0.81/1.02      inference('sup-', [status(thm)], ['15', '55'])).
% 0.81/1.02  thf('57', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X0 @ 
% 0.81/1.02             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.81/1.02          | ~ (r2_hidden @ X0 @ 
% 0.81/1.02               (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A))))),
% 0.81/1.02      inference('simplify', [status(thm)], ['56'])).
% 0.81/1.02  thf('58', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((r2_hidden @ 
% 0.81/1.02           (sk_C @ X1 @ 
% 0.81/1.02            (k5_xboole_0 @ X0 @ 
% 0.81/1.02             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))) @ 
% 0.81/1.02           X0)
% 0.81/1.02          | (r1_tarski @ 
% 0.81/1.02             (k5_xboole_0 @ X0 @ 
% 0.81/1.02              (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))) @ 
% 0.81/1.02             X1)
% 0.81/1.02          | ~ (r2_hidden @ 
% 0.81/1.02               (sk_C @ X1 @ 
% 0.81/1.02                (k5_xboole_0 @ X0 @ 
% 0.81/1.02                 (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))) @ 
% 0.81/1.02               (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A))))),
% 0.81/1.02      inference('sup-', [status(thm)], ['14', '57'])).
% 0.81/1.02  thf('59', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('60', plain,
% 0.81/1.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['3', '4'])).
% 0.81/1.02  thf('61', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.81/1.02           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['6', '7'])).
% 0.81/1.02  thf('62', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.81/1.02           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['60', '61'])).
% 0.81/1.02  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('64', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.02      inference('demod', [status(thm)], ['43', '44'])).
% 0.81/1.02  thf('65', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((X1) = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['63', '64'])).
% 0.81/1.02  thf('66', plain,
% 0.81/1.02      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.81/1.02      inference('demod', [status(thm)], ['62', '65'])).
% 0.81/1.02  thf('67', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['59', '66'])).
% 0.81/1.02  thf('68', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['46', '47'])).
% 0.81/1.02  thf('69', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['67', '68'])).
% 0.81/1.02  thf('70', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((r2_hidden @ 
% 0.81/1.02           (sk_C @ X1 @ 
% 0.81/1.02            (k5_xboole_0 @ X0 @ 
% 0.81/1.02             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))) @ 
% 0.81/1.02           X0)
% 0.81/1.02          | (r1_tarski @ 
% 0.81/1.02             (k5_xboole_0 @ X0 @ 
% 0.81/1.02              (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))) @ 
% 0.81/1.02             X1)
% 0.81/1.02          | ~ (r2_hidden @ 
% 0.81/1.02               (sk_C @ X1 @ 
% 0.81/1.02                (k5_xboole_0 @ X0 @ 
% 0.81/1.02                 (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))) @ 
% 0.81/1.02               (k1_tarski @ sk_A)))),
% 0.81/1.02      inference('demod', [status(thm)], ['58', '69'])).
% 0.81/1.02  thf('71', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         (~ (r2_hidden @ 
% 0.81/1.02             (sk_C @ X2 @ 
% 0.81/1.02              (k5_xboole_0 @ X1 @ 
% 0.81/1.02               (k5_xboole_0 @ X0 @ 
% 0.81/1.02                (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))) @ 
% 0.81/1.02             (k1_tarski @ sk_A))
% 0.81/1.02          | (r1_tarski @ 
% 0.81/1.02             (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 0.81/1.02              (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))) @ 
% 0.81/1.02             X2)
% 0.81/1.02          | (r2_hidden @ 
% 0.81/1.02             (sk_C @ X2 @ 
% 0.81/1.02              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 0.81/1.02               (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))) @ 
% 0.81/1.02             (k5_xboole_0 @ X1 @ X0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['13', '70'])).
% 0.81/1.02  thf('72', plain,
% 0.81/1.02      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.81/1.02           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.81/1.02  thf('73', plain,
% 0.81/1.02      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.81/1.02           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.81/1.02  thf('74', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         (~ (r2_hidden @ 
% 0.81/1.02             (sk_C @ X2 @ 
% 0.81/1.02              (k5_xboole_0 @ X1 @ 
% 0.81/1.02               (k5_xboole_0 @ X0 @ 
% 0.81/1.02                (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))) @ 
% 0.81/1.02             (k1_tarski @ sk_A))
% 0.81/1.02          | (r1_tarski @ 
% 0.81/1.02             (k5_xboole_0 @ X1 @ 
% 0.81/1.02              (k5_xboole_0 @ X0 @ 
% 0.81/1.02               (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))) @ 
% 0.81/1.02             X2)
% 0.81/1.02          | (r2_hidden @ 
% 0.81/1.02             (sk_C @ X2 @ 
% 0.81/1.02              (k5_xboole_0 @ X1 @ 
% 0.81/1.02               (k5_xboole_0 @ X0 @ 
% 0.81/1.02                (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))) @ 
% 0.81/1.02             (k5_xboole_0 @ X1 @ X0)))),
% 0.81/1.02      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.81/1.02  thf('75', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         (~ (r2_hidden @ 
% 0.81/1.02             (sk_C @ X1 @ 
% 0.81/1.02              (k5_xboole_0 @ X0 @ 
% 0.81/1.02               (k4_xboole_0 @ 
% 0.81/1.02                (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.81/1.02                (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))) @ 
% 0.81/1.02             (k1_tarski @ sk_A))
% 0.81/1.02          | (r2_hidden @ 
% 0.81/1.02             (sk_C @ X1 @ 
% 0.81/1.02              (k5_xboole_0 @ X0 @ 
% 0.81/1.02               (k5_xboole_0 @ 
% 0.81/1.02                (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.81/1.02                (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))) @ 
% 0.81/1.02             (k5_xboole_0 @ X0 @ 
% 0.81/1.02              (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))
% 0.81/1.02          | (r1_tarski @ 
% 0.81/1.02             (k5_xboole_0 @ X0 @ 
% 0.81/1.02              (k5_xboole_0 @ 
% 0.81/1.02               (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.81/1.02               (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))) @ 
% 0.81/1.02             X1))),
% 0.81/1.02      inference('sup-', [status(thm)], ['12', '74'])).
% 0.81/1.02  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('77', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.02      inference('demod', [status(thm)], ['43', '44'])).
% 0.81/1.02  thf('78', plain,
% 0.81/1.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['3', '4'])).
% 0.81/1.02  thf('79', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('80', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.02      inference('demod', [status(thm)], ['43', '44'])).
% 0.81/1.02  thf('81', plain,
% 0.81/1.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['3', '4'])).
% 0.81/1.02  thf('82', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('83', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.02      inference('demod', [status(thm)], ['43', '44'])).
% 0.81/1.02  thf('84', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_tarski @ sk_A))
% 0.81/1.02          | (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 0.81/1.02             (k5_xboole_0 @ X0 @ 
% 0.81/1.02              (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))
% 0.81/1.02          | (r1_tarski @ X0 @ X1))),
% 0.81/1.02      inference('demod', [status(thm)],
% 0.81/1.02                ['75', '76', '77', '78', '79', '80', '81', '82', '83'])).
% 0.81/1.02  thf('85', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((r2_hidden @ (sk_C @ X1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)) @ 
% 0.81/1.02           X0)
% 0.81/1.02          | (r1_tarski @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ X1)
% 0.81/1.02          | (r1_tarski @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ X1)
% 0.81/1.02          | (r2_hidden @ 
% 0.81/1.02             (sk_C @ X1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)) @ 
% 0.81/1.02             (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ 
% 0.81/1.02              (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))))),
% 0.81/1.02      inference('sup-', [status(thm)], ['11', '84'])).
% 0.81/1.02  thf('86', plain,
% 0.81/1.02      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.81/1.02           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.81/1.02  thf('87', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((r2_hidden @ (sk_C @ X1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)) @ 
% 0.81/1.02           X0)
% 0.81/1.02          | (r1_tarski @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ X1)
% 0.81/1.02          | (r1_tarski @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ X1)
% 0.81/1.02          | (r2_hidden @ 
% 0.81/1.02             (sk_C @ X1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)) @ 
% 0.81/1.02             (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.81/1.02              (k5_xboole_0 @ X0 @ 
% 0.81/1.02               (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))))),
% 0.81/1.02      inference('demod', [status(thm)], ['85', '86'])).
% 0.81/1.02  thf('88', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((r2_hidden @ (sk_C @ X1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)) @ 
% 0.81/1.02           (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.81/1.02            (k5_xboole_0 @ X0 @ 
% 0.81/1.02             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))))
% 0.81/1.02          | (r1_tarski @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ X1)
% 0.81/1.02          | (r2_hidden @ 
% 0.81/1.02             (sk_C @ X1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)) @ X0))),
% 0.81/1.02      inference('simplify', [status(thm)], ['87'])).
% 0.81/1.02  thf('89', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((r2_hidden @ 
% 0.81/1.02           (sk_C @ X1 @ 
% 0.81/1.02            (k5_xboole_0 @ 
% 0.81/1.02             (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)) @ X0)) @ 
% 0.81/1.02           (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.81/1.02            (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ 
% 0.81/1.02             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))))
% 0.81/1.02          | (r2_hidden @ 
% 0.81/1.02             (sk_C @ X1 @ 
% 0.81/1.02              (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.81/1.02               (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))) @ 
% 0.81/1.02             (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.81/1.02          | (r1_tarski @ 
% 0.81/1.02             (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.81/1.02              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)) @ 
% 0.81/1.02             X1))),
% 0.81/1.02      inference('sup+', [status(thm)], ['8', '88'])).
% 0.81/1.02  thf('90', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('91', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['59', '66'])).
% 0.81/1.02  thf('92', plain,
% 0.81/1.02      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.81/1.02           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.81/1.02  thf('93', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.81/1.02           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['6', '7'])).
% 0.81/1.02  thf('94', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('95', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['59', '66'])).
% 0.81/1.02  thf('96', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.81/1.02           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['6', '7'])).
% 0.81/1.02  thf('97', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('98', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['59', '66'])).
% 0.81/1.02  thf('99', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.81/1.02           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['6', '7'])).
% 0.81/1.02  thf('100', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('101', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['59', '66'])).
% 0.81/1.02  thf('102', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((r2_hidden @ (sk_C @ X1 @ X0) @ 
% 0.81/1.02           (k5_xboole_0 @ X0 @ 
% 0.81/1.02            (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))
% 0.81/1.02          | (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 0.81/1.02             (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.81/1.02          | (r1_tarski @ X0 @ X1))),
% 0.81/1.02      inference('demod', [status(thm)],
% 0.81/1.02                ['89', '90', '91', '92', '93', '94', '95', '96', '97', '98', 
% 0.81/1.02                 '99', '100', '101'])).
% 0.81/1.02  thf('103', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         ((r2_hidden @ 
% 0.81/1.02           (sk_C @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))) @ 
% 0.81/1.02           (k4_xboole_0 @ 
% 0.81/1.02            (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.81/1.02            (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))
% 0.81/1.02          | (r1_tarski @ 
% 0.81/1.02             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)
% 0.81/1.02          | (r2_hidden @ 
% 0.81/1.02             (sk_C @ X0 @ 
% 0.81/1.02              (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))) @ 
% 0.81/1.02             (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.81/1.02              (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))))),
% 0.81/1.02      inference('sup+', [status(thm)], ['5', '102'])).
% 0.81/1.02  thf('104', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('105', plain,
% 0.81/1.02      (![X25 : $i, X26 : $i]:
% 0.81/1.02         ((k2_xboole_0 @ X25 @ X26)
% 0.81/1.02           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.81/1.02  thf('106', plain,
% 0.81/1.02      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.81/1.02         = (k1_tarski @ sk_A))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('107', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         ((r2_hidden @ 
% 0.81/1.02           (sk_C @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))) @ 
% 0.81/1.02           k1_xboole_0)
% 0.81/1.02          | (r1_tarski @ 
% 0.81/1.02             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)
% 0.81/1.02          | (r2_hidden @ 
% 0.81/1.02             (sk_C @ X0 @ 
% 0.81/1.02              (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))) @ 
% 0.81/1.02             (k1_tarski @ sk_A)))),
% 0.81/1.02      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.81/1.02  thf('108', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('109', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.81/1.02      inference('clc', [status(thm)], ['28', '35'])).
% 0.81/1.02  thf('110', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.81/1.02      inference('sup-', [status(thm)], ['108', '109'])).
% 0.81/1.02  thf('111', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         ((r2_hidden @ 
% 0.81/1.02           (sk_C @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))) @ 
% 0.81/1.02           (k1_tarski @ sk_A))
% 0.81/1.02          | (r1_tarski @ 
% 0.81/1.02             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0))),
% 0.81/1.02      inference('clc', [status(thm)], ['107', '110'])).
% 0.81/1.02  thf('112', plain,
% 0.81/1.02      (![X3 : $i, X5 : $i]:
% 0.81/1.02         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.81/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.81/1.02  thf('113', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X2 @ X1)
% 0.81/1.02          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.81/1.02      inference('clc', [status(thm)], ['31', '34'])).
% 0.81/1.02  thf('114', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.81/1.02          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['112', '113'])).
% 0.81/1.02  thf('115', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         (r1_tarski @ 
% 0.81/1.02          (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)),
% 0.81/1.02      inference('clc', [status(thm)], ['111', '114'])).
% 0.81/1.02  thf('116', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('117', plain,
% 0.81/1.02      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['38', '39'])).
% 0.81/1.02  thf('118', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['116', '117'])).
% 0.81/1.02  thf('119', plain,
% 0.81/1.02      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['115', '118'])).
% 0.81/1.02  thf('120', plain,
% 0.81/1.02      (![X14 : $i, X15 : $i]:
% 0.81/1.02         ((k4_xboole_0 @ X14 @ X15)
% 0.81/1.02           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.81/1.02  thf('121', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.81/1.02           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['6', '7'])).
% 0.81/1.02  thf('122', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('123', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('124', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['122', '123'])).
% 0.81/1.02  thf('125', plain,
% 0.81/1.02      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.81/1.02      inference('demod', [status(thm)], ['62', '65'])).
% 0.81/1.02  thf('126', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.81/1.02      inference('sup+', [status(thm)], ['124', '125'])).
% 0.81/1.02  thf('127', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.81/1.02      inference('demod', [status(thm)], ['121', '126'])).
% 0.81/1.02  thf('128', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k3_xboole_0 @ X1 @ X0)
% 0.81/1.02           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['120', '127'])).
% 0.81/1.02  thf('129', plain,
% 0.81/1.02      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.81/1.02         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['119', '128'])).
% 0.81/1.02  thf('130', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.02      inference('demod', [status(thm)], ['43', '44'])).
% 0.81/1.02  thf('131', plain,
% 0.81/1.02      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.81/1.02         = (k1_tarski @ sk_B))),
% 0.81/1.02      inference('demod', [status(thm)], ['129', '130'])).
% 0.81/1.02  thf('132', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.81/1.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.81/1.02  thf('133', plain,
% 0.81/1.02      (![X14 : $i, X15 : $i]:
% 0.81/1.02         ((k4_xboole_0 @ X14 @ X15)
% 0.81/1.02           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.81/1.02  thf('134', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k4_xboole_0 @ X0 @ X1)
% 0.81/1.02           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['132', '133'])).
% 0.81/1.02  thf('135', plain,
% 0.81/1.02      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.81/1.02         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['131', '134'])).
% 0.81/1.02  thf('136', plain,
% 0.81/1.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['3', '4'])).
% 0.81/1.02  thf('137', plain,
% 0.81/1.02      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.81/1.02           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.81/1.02  thf('138', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.81/1.02           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.81/1.02      inference('sup+', [status(thm)], ['136', '137'])).
% 0.81/1.02  thf('139', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '40'])).
% 0.81/1.02  thf('140', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k1_xboole_0)
% 0.81/1.02           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.81/1.02      inference('demod', [status(thm)], ['138', '139'])).
% 0.81/1.02  thf('141', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.81/1.02      inference('demod', [status(thm)], ['121', '126'])).
% 0.81/1.02  thf('142', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.81/1.02           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['140', '141'])).
% 0.81/1.02  thf('143', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.02      inference('demod', [status(thm)], ['43', '44'])).
% 0.81/1.02  thf('144', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.81/1.02      inference('demod', [status(thm)], ['142', '143'])).
% 0.81/1.02  thf('145', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.81/1.02      inference('demod', [status(thm)], ['121', '126'])).
% 0.81/1.02  thf('146', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['144', '145'])).
% 0.81/1.02  thf('147', plain,
% 0.81/1.02      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.81/1.02         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.81/1.02      inference('demod', [status(thm)], ['135', '146'])).
% 0.81/1.02  thf('148', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.81/1.02      inference('demod', [status(thm)], ['121', '126'])).
% 0.81/1.02  thf('149', plain,
% 0.81/1.02      (((k1_tarski @ sk_A)
% 0.81/1.02         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.81/1.02            (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 0.81/1.02      inference('sup+', [status(thm)], ['147', '148'])).
% 0.81/1.02  thf('150', plain,
% 0.81/1.02      (![X25 : $i, X26 : $i]:
% 0.81/1.02         ((k2_xboole_0 @ X25 @ X26)
% 0.81/1.02           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.81/1.02  thf('151', plain,
% 0.81/1.02      (((k1_tarski @ sk_A)
% 0.81/1.02         = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.81/1.02      inference('demod', [status(thm)], ['149', '150'])).
% 0.81/1.02  thf('152', plain,
% 0.81/1.02      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.81/1.02      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.81/1.02  thf('153', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 0.81/1.02      inference('sup+', [status(thm)], ['151', '152'])).
% 0.81/1.02  thf(t6_zfmisc_1, axiom,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.81/1.02       ( ( A ) = ( B ) ) ))).
% 0.81/1.02  thf('154', plain,
% 0.81/1.02      (![X37 : $i, X38 : $i]:
% 0.81/1.02         (((X38) = (X37))
% 0.81/1.02          | ~ (r1_tarski @ (k1_tarski @ X38) @ (k1_tarski @ X37)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.81/1.02  thf('155', plain, (((sk_B) = (sk_A))),
% 0.81/1.02      inference('sup-', [status(thm)], ['153', '154'])).
% 0.81/1.02  thf('156', plain, (((sk_A) != (sk_B))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('157', plain, ($false),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)], ['155', '156'])).
% 0.81/1.02  
% 0.81/1.02  % SZS output end Refutation
% 0.81/1.02  
% 0.81/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
