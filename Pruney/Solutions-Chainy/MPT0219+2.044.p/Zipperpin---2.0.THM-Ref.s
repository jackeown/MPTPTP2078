%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BT2A0wVWKA

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:09 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 259 expanded)
%              Number of leaves         :   25 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  912 (2033 expanded)
%              Number of equality atoms :   70 ( 175 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ( X16 != X17 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X17: $i] :
      ( r1_tarski @ X17 @ X17 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( X3
        = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('33',plain,(
    ! [X28: $i] :
      ( r1_tarski @ k1_xboole_0 @ X28 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    ! [X16: $i,X18: $i] :
      ( ( X16 = X18 )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','36'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','40'])).

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

thf('42',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('44',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k5_xboole_0 @ X13 @ X15 ) )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['42','54'])).

thf('56',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('59',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('62',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('69',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_xboole_0 @ X22 @ X21 )
        = X21 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,
    ( ( k1_tarski @ sk_B )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('75',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X17: $i] :
      ( r1_tarski @ X17 @ X17 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('78',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_xboole_0 @ X22 @ X21 )
        = X21 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['73','80'])).

thf('82',plain,
    ( ( k1_tarski @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('87',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X42 = X41 )
      | ~ ( r1_tarski @ ( k1_tarski @ X42 ) @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('88',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BT2A0wVWKA
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.84/2.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.84/2.07  % Solved by: fo/fo7.sh
% 1.84/2.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.84/2.07  % done 2513 iterations in 1.618s
% 1.84/2.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.84/2.07  % SZS output start Refutation
% 1.84/2.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.84/2.07  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.84/2.07  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.84/2.07  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.84/2.07  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.84/2.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.84/2.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.84/2.07  thf(sk_B_type, type, sk_B: $i).
% 1.84/2.07  thf(sk_A_type, type, sk_A: $i).
% 1.84/2.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.84/2.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.84/2.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.84/2.07  thf(d10_xboole_0, axiom,
% 1.84/2.07    (![A:$i,B:$i]:
% 1.84/2.07     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.84/2.07  thf('0', plain,
% 1.84/2.07      (![X16 : $i, X17 : $i]: ((r1_tarski @ X16 @ X17) | ((X16) != (X17)))),
% 1.84/2.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.84/2.07  thf('1', plain, (![X17 : $i]: (r1_tarski @ X17 @ X17)),
% 1.84/2.07      inference('simplify', [status(thm)], ['0'])).
% 1.84/2.07  thf(t28_xboole_1, axiom,
% 1.84/2.07    (![A:$i,B:$i]:
% 1.84/2.07     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.84/2.07  thf('2', plain,
% 1.84/2.07      (![X26 : $i, X27 : $i]:
% 1.84/2.07         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 1.84/2.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.84/2.07  thf('3', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.84/2.07      inference('sup-', [status(thm)], ['1', '2'])).
% 1.84/2.07  thf(d5_xboole_0, axiom,
% 1.84/2.07    (![A:$i,B:$i,C:$i]:
% 1.84/2.07     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.84/2.07       ( ![D:$i]:
% 1.84/2.07         ( ( r2_hidden @ D @ C ) <=>
% 1.84/2.07           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.84/2.07  thf('4', plain,
% 1.84/2.07      (![X7 : $i, X8 : $i, X11 : $i]:
% 1.84/2.07         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 1.84/2.07          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 1.84/2.07          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 1.84/2.07      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.84/2.07  thf(t17_xboole_1, axiom,
% 1.84/2.07    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.84/2.07  thf('5', plain,
% 1.84/2.07      (![X23 : $i, X24 : $i]: (r1_tarski @ (k3_xboole_0 @ X23 @ X24) @ X23)),
% 1.84/2.07      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.84/2.07  thf(d3_tarski, axiom,
% 1.84/2.07    (![A:$i,B:$i]:
% 1.84/2.07     ( ( r1_tarski @ A @ B ) <=>
% 1.84/2.07       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.84/2.07  thf('6', plain,
% 1.84/2.07      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.84/2.07         (~ (r2_hidden @ X2 @ X3)
% 1.84/2.07          | (r2_hidden @ X2 @ X4)
% 1.84/2.07          | ~ (r1_tarski @ X3 @ X4))),
% 1.84/2.07      inference('cnf', [status(esa)], [d3_tarski])).
% 1.84/2.07  thf('7', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.84/2.07         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.84/2.07      inference('sup-', [status(thm)], ['5', '6'])).
% 1.84/2.07  thf('8', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.84/2.07         ((r2_hidden @ (sk_D @ X3 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 1.84/2.07          | ((X3) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 1.84/2.07          | (r2_hidden @ (sk_D @ X3 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 1.84/2.07      inference('sup-', [status(thm)], ['4', '7'])).
% 1.84/2.07  thf('9', plain,
% 1.84/2.07      (![X7 : $i, X8 : $i, X11 : $i]:
% 1.84/2.07         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 1.84/2.07          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 1.84/2.07          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 1.84/2.07      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.84/2.07  thf('10', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.84/2.07         (((X2) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))
% 1.84/2.07          | (r2_hidden @ (sk_D @ X2 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ X2)
% 1.84/2.07          | (r2_hidden @ (sk_D @ X2 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ X2)
% 1.84/2.07          | ((X2) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)))),
% 1.84/2.07      inference('sup-', [status(thm)], ['8', '9'])).
% 1.84/2.07  thf('11', plain,
% 1.84/2.07      (![X23 : $i, X24 : $i]: (r1_tarski @ (k3_xboole_0 @ X23 @ X24) @ X23)),
% 1.84/2.07      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.84/2.07  thf('12', plain,
% 1.84/2.07      (![X26 : $i, X27 : $i]:
% 1.84/2.07         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 1.84/2.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.84/2.07  thf('13', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.84/2.07           = (k3_xboole_0 @ X0 @ X1))),
% 1.84/2.07      inference('sup-', [status(thm)], ['11', '12'])).
% 1.84/2.07  thf(commutativity_k3_xboole_0, axiom,
% 1.84/2.07    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.84/2.07  thf('14', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.84/2.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.84/2.07  thf('15', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.84/2.07           = (k3_xboole_0 @ X0 @ X1))),
% 1.84/2.07      inference('demod', [status(thm)], ['13', '14'])).
% 1.84/2.07  thf('16', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.84/2.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.84/2.07  thf(t100_xboole_1, axiom,
% 1.84/2.07    (![A:$i,B:$i]:
% 1.84/2.07     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.84/2.07  thf('17', plain,
% 1.84/2.07      (![X19 : $i, X20 : $i]:
% 1.84/2.07         ((k4_xboole_0 @ X19 @ X20)
% 1.84/2.07           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 1.84/2.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.84/2.07  thf('18', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         ((k4_xboole_0 @ X0 @ X1)
% 1.84/2.07           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.84/2.07      inference('sup+', [status(thm)], ['16', '17'])).
% 1.84/2.07  thf('19', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 1.84/2.07           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.84/2.07      inference('sup+', [status(thm)], ['15', '18'])).
% 1.84/2.07  thf('20', plain,
% 1.84/2.07      (![X3 : $i, X5 : $i]:
% 1.84/2.07         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.84/2.07      inference('cnf', [status(esa)], [d3_tarski])).
% 1.84/2.07  thf('21', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.84/2.07      inference('sup-', [status(thm)], ['1', '2'])).
% 1.84/2.07  thf('22', plain,
% 1.84/2.07      (![X19 : $i, X20 : $i]:
% 1.84/2.07         ((k4_xboole_0 @ X19 @ X20)
% 1.84/2.07           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 1.84/2.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.84/2.07  thf('23', plain,
% 1.84/2.07      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.84/2.07      inference('sup+', [status(thm)], ['21', '22'])).
% 1.84/2.07  thf('24', plain,
% 1.84/2.07      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.84/2.07         (~ (r2_hidden @ X10 @ X9)
% 1.84/2.07          | (r2_hidden @ X10 @ X7)
% 1.84/2.07          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.84/2.07      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.84/2.07  thf('25', plain,
% 1.84/2.07      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.84/2.07         ((r2_hidden @ X10 @ X7)
% 1.84/2.07          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.84/2.07      inference('simplify', [status(thm)], ['24'])).
% 1.84/2.07  thf('26', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 1.84/2.07      inference('sup-', [status(thm)], ['23', '25'])).
% 1.84/2.07  thf('27', plain,
% 1.84/2.07      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.84/2.07      inference('sup+', [status(thm)], ['21', '22'])).
% 1.84/2.07  thf('28', plain,
% 1.84/2.07      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.84/2.07         (~ (r2_hidden @ X10 @ X9)
% 1.84/2.07          | ~ (r2_hidden @ X10 @ X8)
% 1.84/2.07          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.84/2.07      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.84/2.07  thf('29', plain,
% 1.84/2.07      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.84/2.07         (~ (r2_hidden @ X10 @ X8)
% 1.84/2.07          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.84/2.07      inference('simplify', [status(thm)], ['28'])).
% 1.84/2.07  thf('30', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 1.84/2.07          | ~ (r2_hidden @ X1 @ X0))),
% 1.84/2.07      inference('sup-', [status(thm)], ['27', '29'])).
% 1.84/2.07  thf('31', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 1.84/2.07      inference('clc', [status(thm)], ['26', '30'])).
% 1.84/2.07  thf('32', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 1.84/2.07      inference('sup-', [status(thm)], ['20', '31'])).
% 1.84/2.07  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.84/2.07  thf('33', plain, (![X28 : $i]: (r1_tarski @ k1_xboole_0 @ X28)),
% 1.84/2.07      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.84/2.07  thf('34', plain,
% 1.84/2.07      (![X16 : $i, X18 : $i]:
% 1.84/2.07         (((X16) = (X18))
% 1.84/2.07          | ~ (r1_tarski @ X18 @ X16)
% 1.84/2.07          | ~ (r1_tarski @ X16 @ X18))),
% 1.84/2.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.84/2.07  thf('35', plain,
% 1.84/2.07      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.84/2.07      inference('sup-', [status(thm)], ['33', '34'])).
% 1.84/2.07  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.84/2.07      inference('sup-', [status(thm)], ['32', '35'])).
% 1.84/2.07  thf('37', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.84/2.07      inference('demod', [status(thm)], ['19', '36'])).
% 1.84/2.07  thf('38', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.84/2.07      inference('demod', [status(thm)], ['19', '36'])).
% 1.84/2.07  thf('39', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.84/2.07         (((X2) = (k1_xboole_0))
% 1.84/2.07          | (r2_hidden @ (sk_D @ X2 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ X2)
% 1.84/2.07          | (r2_hidden @ (sk_D @ X2 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ X2)
% 1.84/2.07          | ((X2) = (k1_xboole_0)))),
% 1.84/2.07      inference('demod', [status(thm)], ['10', '37', '38'])).
% 1.84/2.07  thf('40', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.84/2.07         ((r2_hidden @ (sk_D @ X2 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ X2)
% 1.84/2.07          | ((X2) = (k1_xboole_0)))),
% 1.84/2.07      inference('simplify', [status(thm)], ['39'])).
% 1.84/2.07  thf('41', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1) | ((X1) = (k1_xboole_0)))),
% 1.84/2.07      inference('sup+', [status(thm)], ['3', '40'])).
% 1.84/2.07  thf(t13_zfmisc_1, conjecture,
% 1.84/2.07    (![A:$i,B:$i]:
% 1.84/2.07     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.84/2.07         ( k1_tarski @ A ) ) =>
% 1.84/2.07       ( ( A ) = ( B ) ) ))).
% 1.84/2.07  thf(zf_stmt_0, negated_conjecture,
% 1.84/2.07    (~( ![A:$i,B:$i]:
% 1.84/2.07        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.84/2.07            ( k1_tarski @ A ) ) =>
% 1.84/2.07          ( ( A ) = ( B ) ) ) )),
% 1.84/2.07    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 1.84/2.07  thf('42', plain,
% 1.84/2.07      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.84/2.07         = (k1_tarski @ sk_A))),
% 1.84/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.84/2.07  thf(t98_xboole_1, axiom,
% 1.84/2.07    (![A:$i,B:$i]:
% 1.84/2.07     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.84/2.07  thf('43', plain,
% 1.84/2.07      (![X29 : $i, X30 : $i]:
% 1.84/2.07         ((k2_xboole_0 @ X29 @ X30)
% 1.84/2.07           = (k5_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29)))),
% 1.84/2.07      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.84/2.07  thf('44', plain,
% 1.84/2.07      (![X3 : $i, X5 : $i]:
% 1.84/2.07         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.84/2.07      inference('cnf', [status(esa)], [d3_tarski])).
% 1.84/2.07  thf(t1_xboole_0, axiom,
% 1.84/2.07    (![A:$i,B:$i,C:$i]:
% 1.84/2.07     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.84/2.07       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.84/2.07  thf('45', plain,
% 1.84/2.07      (![X12 : $i, X13 : $i, X15 : $i]:
% 1.84/2.07         ((r2_hidden @ X12 @ (k5_xboole_0 @ X13 @ X15))
% 1.84/2.07          | (r2_hidden @ X12 @ X13)
% 1.84/2.07          | ~ (r2_hidden @ X12 @ X15))),
% 1.84/2.07      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.84/2.07  thf('46', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.84/2.07         ((r1_tarski @ X0 @ X1)
% 1.84/2.07          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 1.84/2.07          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k5_xboole_0 @ X2 @ X0)))),
% 1.84/2.07      inference('sup-', [status(thm)], ['44', '45'])).
% 1.84/2.07  thf('47', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.84/2.07         ((r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 1.84/2.07           (k2_xboole_0 @ X1 @ X0))
% 1.84/2.07          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ X1)
% 1.84/2.07          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 1.84/2.07      inference('sup+', [status(thm)], ['43', '46'])).
% 1.84/2.07  thf('48', plain,
% 1.84/2.07      (![X3 : $i, X5 : $i]:
% 1.84/2.07         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.84/2.07      inference('cnf', [status(esa)], [d3_tarski])).
% 1.84/2.07  thf('49', plain,
% 1.84/2.07      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.84/2.07         (~ (r2_hidden @ X10 @ X8)
% 1.84/2.07          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.84/2.07      inference('simplify', [status(thm)], ['28'])).
% 1.84/2.07  thf('50', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.84/2.07         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.84/2.07          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 1.84/2.07      inference('sup-', [status(thm)], ['48', '49'])).
% 1.84/2.07  thf('51', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.84/2.07         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 1.84/2.07          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 1.84/2.07             (k2_xboole_0 @ X1 @ X0)))),
% 1.84/2.07      inference('clc', [status(thm)], ['47', '50'])).
% 1.84/2.07  thf('52', plain,
% 1.84/2.07      (![X3 : $i, X5 : $i]:
% 1.84/2.07         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 1.84/2.07      inference('cnf', [status(esa)], [d3_tarski])).
% 1.84/2.07  thf('53', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 1.84/2.07          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.84/2.07      inference('sup-', [status(thm)], ['51', '52'])).
% 1.84/2.07  thf('54', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 1.84/2.07      inference('simplify', [status(thm)], ['53'])).
% 1.84/2.07  thf('55', plain,
% 1.84/2.07      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 1.84/2.07        (k1_tarski @ sk_A))),
% 1.84/2.07      inference('sup+', [status(thm)], ['42', '54'])).
% 1.84/2.07  thf('56', plain,
% 1.84/2.07      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.84/2.07         (~ (r2_hidden @ X2 @ X3)
% 1.84/2.07          | (r2_hidden @ X2 @ X4)
% 1.84/2.07          | ~ (r1_tarski @ X3 @ X4))),
% 1.84/2.07      inference('cnf', [status(esa)], [d3_tarski])).
% 1.84/2.07  thf('57', plain,
% 1.84/2.07      (![X0 : $i]:
% 1.84/2.07         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.84/2.07          | ~ (r2_hidden @ X0 @ 
% 1.84/2.07               (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))),
% 1.84/2.07      inference('sup-', [status(thm)], ['55', '56'])).
% 1.84/2.07  thf('58', plain,
% 1.84/2.07      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.84/2.07         (~ (r2_hidden @ X10 @ X8)
% 1.84/2.07          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.84/2.07      inference('simplify', [status(thm)], ['28'])).
% 1.84/2.07  thf('59', plain,
% 1.84/2.07      (![X0 : $i]:
% 1.84/2.07         ~ (r2_hidden @ X0 @ 
% 1.84/2.07            (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 1.84/2.07      inference('clc', [status(thm)], ['57', '58'])).
% 1.84/2.07  thf('60', plain,
% 1.84/2.07      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 1.84/2.07      inference('sup-', [status(thm)], ['41', '59'])).
% 1.84/2.07  thf('61', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.84/2.07           = (k3_xboole_0 @ X0 @ X1))),
% 1.84/2.07      inference('demod', [status(thm)], ['13', '14'])).
% 1.84/2.07  thf('62', plain,
% 1.84/2.07      (![X19 : $i, X20 : $i]:
% 1.84/2.07         ((k4_xboole_0 @ X19 @ X20)
% 1.84/2.07           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 1.84/2.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.84/2.07  thf('63', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.84/2.07           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.84/2.07      inference('sup+', [status(thm)], ['61', '62'])).
% 1.84/2.07  thf('64', plain,
% 1.84/2.07      (![X19 : $i, X20 : $i]:
% 1.84/2.07         ((k4_xboole_0 @ X19 @ X20)
% 1.84/2.07           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 1.84/2.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.84/2.07  thf('65', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.84/2.07           = (k4_xboole_0 @ X1 @ X0))),
% 1.84/2.07      inference('demod', [status(thm)], ['63', '64'])).
% 1.84/2.07  thf('66', plain,
% 1.84/2.07      (![X29 : $i, X30 : $i]:
% 1.84/2.07         ((k2_xboole_0 @ X29 @ X30)
% 1.84/2.07           = (k5_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29)))),
% 1.84/2.07      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.84/2.07  thf('67', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 1.84/2.07           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.84/2.07      inference('sup+', [status(thm)], ['65', '66'])).
% 1.84/2.07  thf('68', plain,
% 1.84/2.07      (![X23 : $i, X24 : $i]: (r1_tarski @ (k3_xboole_0 @ X23 @ X24) @ X23)),
% 1.84/2.07      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.84/2.07  thf(t12_xboole_1, axiom,
% 1.84/2.07    (![A:$i,B:$i]:
% 1.84/2.07     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.84/2.07  thf('69', plain,
% 1.84/2.07      (![X21 : $i, X22 : $i]:
% 1.84/2.07         (((k2_xboole_0 @ X22 @ X21) = (X21)) | ~ (r1_tarski @ X22 @ X21))),
% 1.84/2.07      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.84/2.07  thf('70', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.84/2.07      inference('sup-', [status(thm)], ['68', '69'])).
% 1.84/2.07  thf('71', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]:
% 1.84/2.07         ((X1)
% 1.84/2.07           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.84/2.07      inference('demod', [status(thm)], ['67', '70'])).
% 1.84/2.07  thf('72', plain,
% 1.84/2.07      (((k1_tarski @ sk_B)
% 1.84/2.07         = (k5_xboole_0 @ 
% 1.84/2.07            (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 1.84/2.07            k1_xboole_0))),
% 1.84/2.07      inference('sup+', [status(thm)], ['60', '71'])).
% 1.84/2.07  thf('73', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.84/2.07      inference('sup-', [status(thm)], ['32', '35'])).
% 1.84/2.07  thf('74', plain,
% 1.84/2.07      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.84/2.07      inference('sup+', [status(thm)], ['21', '22'])).
% 1.84/2.07  thf('75', plain,
% 1.84/2.07      (![X29 : $i, X30 : $i]:
% 1.84/2.07         ((k2_xboole_0 @ X29 @ X30)
% 1.84/2.07           = (k5_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29)))),
% 1.84/2.07      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.84/2.07  thf('76', plain,
% 1.84/2.07      (![X0 : $i]:
% 1.84/2.07         ((k2_xboole_0 @ X0 @ X0)
% 1.84/2.07           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.84/2.07      inference('sup+', [status(thm)], ['74', '75'])).
% 1.84/2.07  thf('77', plain, (![X17 : $i]: (r1_tarski @ X17 @ X17)),
% 1.84/2.07      inference('simplify', [status(thm)], ['0'])).
% 1.84/2.07  thf('78', plain,
% 1.84/2.07      (![X21 : $i, X22 : $i]:
% 1.84/2.07         (((k2_xboole_0 @ X22 @ X21) = (X21)) | ~ (r1_tarski @ X22 @ X21))),
% 1.84/2.07      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.84/2.07  thf('79', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.84/2.07      inference('sup-', [status(thm)], ['77', '78'])).
% 1.84/2.07  thf('80', plain,
% 1.84/2.07      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.84/2.07      inference('demod', [status(thm)], ['76', '79'])).
% 1.84/2.07  thf('81', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.84/2.07      inference('sup+', [status(thm)], ['73', '80'])).
% 1.84/2.07  thf('82', plain,
% 1.84/2.07      (((k1_tarski @ sk_B)
% 1.84/2.07         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 1.84/2.07      inference('demod', [status(thm)], ['72', '81'])).
% 1.84/2.07  thf('83', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.84/2.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.84/2.07  thf('84', plain,
% 1.84/2.07      (![X23 : $i, X24 : $i]: (r1_tarski @ (k3_xboole_0 @ X23 @ X24) @ X23)),
% 1.84/2.07      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.84/2.07  thf('85', plain,
% 1.84/2.07      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.84/2.07      inference('sup+', [status(thm)], ['83', '84'])).
% 1.84/2.07  thf('86', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 1.84/2.07      inference('sup+', [status(thm)], ['82', '85'])).
% 1.84/2.07  thf(t6_zfmisc_1, axiom,
% 1.84/2.07    (![A:$i,B:$i]:
% 1.84/2.07     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 1.84/2.07       ( ( A ) = ( B ) ) ))).
% 1.84/2.07  thf('87', plain,
% 1.84/2.07      (![X41 : $i, X42 : $i]:
% 1.84/2.07         (((X42) = (X41))
% 1.84/2.07          | ~ (r1_tarski @ (k1_tarski @ X42) @ (k1_tarski @ X41)))),
% 1.84/2.07      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 1.84/2.07  thf('88', plain, (((sk_B) = (sk_A))),
% 1.84/2.07      inference('sup-', [status(thm)], ['86', '87'])).
% 1.84/2.07  thf('89', plain, (((sk_A) != (sk_B))),
% 1.84/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.84/2.07  thf('90', plain, ($false),
% 1.84/2.07      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 1.84/2.07  
% 1.84/2.07  % SZS output end Refutation
% 1.84/2.07  
% 1.84/2.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
