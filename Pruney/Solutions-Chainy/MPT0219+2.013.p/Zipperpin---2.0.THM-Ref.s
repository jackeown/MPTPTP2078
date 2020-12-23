%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K9NFbBJSXI

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:05 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  174 (1409 expanded)
%              Number of leaves         :   33 ( 441 expanded)
%              Depth                    :   29
%              Number of atoms          : 1416 (10962 expanded)
%              Number of equality atoms :  117 ( 950 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X41 != X40 )
      | ( r2_hidden @ X41 @ X42 )
      | ( X42
       != ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X40: $i] :
      ( r2_hidden @ X40 @ ( k1_tarski @ X40 ) ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
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

thf('4',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['37','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('54',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('55',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('56',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('59',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('60',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16','51','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','67'])).

thf('69',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','68'])).

thf('70',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('72',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( X29 = X30 )
      | ( X29 = X31 )
      | ( X29 = X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('73',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('74',plain,(
    ! [X40: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X43 @ X42 )
      | ( X43 = X40 )
      | ( X42
       != ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('75',plain,(
    ! [X40: $i,X43: $i] :
      ( ( X43 = X40 )
      | ~ ( r2_hidden @ X43 @ ( k1_tarski @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('79',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('80',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('85',plain,
    ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('87',plain,(
    ! [X49: $i] :
      ( ( k2_tarski @ X49 @ X49 )
      = ( k1_tarski @ X49 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('88',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_enumset1 @ X50 @ X50 @ X51 )
      = ( k2_tarski @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('89',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X38 @ X37 )
      | ~ ( zip_tseitin_0 @ X38 @ X34 @ X35 @ X36 )
      | ( X37
       != ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('90',plain,(
    ! [X34: $i,X35: $i,X36: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X34 @ X35 @ X36 )
      | ~ ( r2_hidden @ X38 @ ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','91'])).

thf('93',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    | ~ ( zip_tseitin_0 @ ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,
    ( ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','93'])).

thf('95',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['72','95'])).

thf('97',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['71','101'])).

thf('103',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','102'])).

thf('104',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','68'])).

thf('105',plain,(
    ! [X40: $i] :
      ( r2_hidden @ X40 @ ( k1_tarski @ X40 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('106',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X10 ) )
      | ( r2_hidden @ X7 @ X10 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['104','107'])).

thf('109',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','102'])).

thf('110',plain,(
    r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('112',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','114'])).

thf('116',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('117',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('119',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('120',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('121',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('122',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16','51','66'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16','51','66'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('134',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('135',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120','121','132','133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('137',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['103','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K9NFbBJSXI
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:36:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.90/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.08  % Solved by: fo/fo7.sh
% 0.90/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.08  % done 956 iterations in 0.615s
% 0.90/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.08  % SZS output start Refutation
% 0.90/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.08  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.90/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.08  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.08  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.90/1.08  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.08  thf(d1_tarski, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.90/1.08       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.90/1.08  thf('0', plain,
% 0.90/1.08      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.90/1.08         (((X41) != (X40))
% 0.90/1.08          | (r2_hidden @ X41 @ X42)
% 0.90/1.08          | ((X42) != (k1_tarski @ X40)))),
% 0.90/1.08      inference('cnf', [status(esa)], [d1_tarski])).
% 0.90/1.08  thf('1', plain, (![X40 : $i]: (r2_hidden @ X40 @ (k1_tarski @ X40))),
% 0.90/1.08      inference('simplify', [status(thm)], ['0'])).
% 0.90/1.08  thf(t13_zfmisc_1, conjecture,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.90/1.08         ( k1_tarski @ A ) ) =>
% 0.90/1.08       ( ( A ) = ( B ) ) ))).
% 0.90/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.08    (~( ![A:$i,B:$i]:
% 0.90/1.08        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.90/1.08            ( k1_tarski @ A ) ) =>
% 0.90/1.08          ( ( A ) = ( B ) ) ) )),
% 0.90/1.08    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.90/1.08  thf('2', plain,
% 0.90/1.08      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.90/1.08         = (k1_tarski @ sk_A))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(commutativity_k2_xboole_0, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.90/1.08  thf('3', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.90/1.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.90/1.08  thf('4', plain,
% 0.90/1.08      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.90/1.08         = (k1_tarski @ sk_A))),
% 0.90/1.08      inference('demod', [status(thm)], ['2', '3'])).
% 0.90/1.08  thf(t98_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.90/1.08  thf('5', plain,
% 0.90/1.08      (![X26 : $i, X27 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ X26 @ X27)
% 0.90/1.08           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.90/1.08  thf(d10_xboole_0, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.08  thf('6', plain,
% 0.90/1.08      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 0.90/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.08  thf('7', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.90/1.08      inference('simplify', [status(thm)], ['6'])).
% 0.90/1.08  thf(t28_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.90/1.08  thf('8', plain,
% 0.90/1.08      (![X16 : $i, X17 : $i]:
% 0.90/1.08         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.90/1.08      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.90/1.08  thf('9', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['7', '8'])).
% 0.90/1.08  thf(t100_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.08  thf('10', plain,
% 0.90/1.08      (![X14 : $i, X15 : $i]:
% 0.90/1.08         ((k4_xboole_0 @ X14 @ X15)
% 0.90/1.08           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.08  thf('11', plain,
% 0.90/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['9', '10'])).
% 0.90/1.08  thf(t91_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.90/1.08       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.90/1.08  thf('12', plain,
% 0.90/1.08      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.08         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.90/1.08           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.90/1.08  thf('13', plain,
% 0.90/1.08      (![X26 : $i, X27 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ X26 @ X27)
% 0.90/1.08           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.90/1.08  thf('14', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.90/1.08           = (k5_xboole_0 @ X1 @ 
% 0.90/1.08              (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 0.90/1.08      inference('sup+', [status(thm)], ['12', '13'])).
% 0.90/1.08  thf('15', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 0.90/1.08           = (k5_xboole_0 @ X0 @ 
% 0.90/1.08              (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))))),
% 0.90/1.08      inference('sup+', [status(thm)], ['11', '14'])).
% 0.90/1.08  thf('16', plain,
% 0.90/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['9', '10'])).
% 0.90/1.08  thf(d3_tarski, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( r1_tarski @ A @ B ) <=>
% 0.90/1.08       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.90/1.08  thf('17', plain,
% 0.90/1.08      (![X3 : $i, X5 : $i]:
% 0.90/1.08         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('18', plain,
% 0.90/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['9', '10'])).
% 0.90/1.08  thf(t1_xboole_0, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.90/1.08       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.90/1.08  thf('19', plain,
% 0.90/1.08      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.90/1.08         ((r2_hidden @ X7 @ X8)
% 0.90/1.08          | (r2_hidden @ X7 @ X9)
% 0.90/1.08          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.90/1.08  thf('20', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.90/1.08          | (r2_hidden @ X1 @ X0)
% 0.90/1.08          | (r2_hidden @ X1 @ X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['18', '19'])).
% 0.90/1.08  thf('21', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['20'])).
% 0.90/1.08  thf('22', plain,
% 0.90/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['9', '10'])).
% 0.90/1.08  thf('23', plain,
% 0.90/1.08      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X7 @ X8)
% 0.90/1.08          | ~ (r2_hidden @ X7 @ X9)
% 0.90/1.08          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.90/1.08  thf('24', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.90/1.08          | ~ (r2_hidden @ X1 @ X0)
% 0.90/1.08          | ~ (r2_hidden @ X1 @ X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['22', '23'])).
% 0.90/1.08  thf('25', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X1 @ X0)
% 0.90/1.08          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['24'])).
% 0.90/1.08  thf('26', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.90/1.08      inference('clc', [status(thm)], ['21', '25'])).
% 0.90/1.08  thf('27', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.90/1.08      inference('sup-', [status(thm)], ['17', '26'])).
% 0.90/1.08  thf('28', plain,
% 0.90/1.08      (![X3 : $i, X5 : $i]:
% 0.90/1.08         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf(t5_boole, axiom,
% 0.90/1.08    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.90/1.08  thf('29', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.90/1.08      inference('cnf', [status(esa)], [t5_boole])).
% 0.90/1.08  thf('30', plain,
% 0.90/1.08      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X7 @ X8)
% 0.90/1.08          | ~ (r2_hidden @ X7 @ X9)
% 0.90/1.08          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.90/1.08  thf('31', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X1 @ X0)
% 0.90/1.08          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.90/1.08          | ~ (r2_hidden @ X1 @ X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['29', '30'])).
% 0.90/1.08  thf('32', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.90/1.08      inference('simplify', [status(thm)], ['31'])).
% 0.90/1.08  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.08      inference('condensation', [status(thm)], ['32'])).
% 0.90/1.08  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.90/1.08      inference('sup-', [status(thm)], ['28', '33'])).
% 0.90/1.08  thf('35', plain,
% 0.90/1.08      (![X11 : $i, X13 : $i]:
% 0.90/1.08         (((X11) = (X13))
% 0.90/1.08          | ~ (r1_tarski @ X13 @ X11)
% 0.90/1.08          | ~ (r1_tarski @ X11 @ X13))),
% 0.90/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.08  thf('36', plain,
% 0.90/1.08      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['34', '35'])).
% 0.90/1.08  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['27', '36'])).
% 0.90/1.08  thf('38', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.90/1.08      inference('sup-', [status(thm)], ['28', '33'])).
% 0.90/1.08  thf('39', plain,
% 0.90/1.08      (![X16 : $i, X17 : $i]:
% 0.90/1.08         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.90/1.08      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.90/1.08  thf('40', plain,
% 0.90/1.08      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['38', '39'])).
% 0.90/1.08  thf('41', plain,
% 0.90/1.08      (![X14 : $i, X15 : $i]:
% 0.90/1.08         ((k4_xboole_0 @ X14 @ X15)
% 0.90/1.08           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.08  thf('42', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.90/1.08           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['40', '41'])).
% 0.90/1.08  thf('43', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.90/1.08      inference('cnf', [status(esa)], [t5_boole])).
% 0.90/1.08  thf('44', plain,
% 0.90/1.08      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.90/1.08      inference('demod', [status(thm)], ['42', '43'])).
% 0.90/1.08  thf('45', plain,
% 0.90/1.08      (![X26 : $i, X27 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ X26 @ X27)
% 0.90/1.08           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.90/1.08  thf('46', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['44', '45'])).
% 0.90/1.08  thf('47', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.90/1.08      inference('cnf', [status(esa)], [t5_boole])).
% 0.90/1.08  thf('48', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['46', '47'])).
% 0.90/1.08  thf('49', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.90/1.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.90/1.08  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['48', '49'])).
% 0.90/1.08  thf('51', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.90/1.08      inference('sup+', [status(thm)], ['37', '50'])).
% 0.90/1.08  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['27', '36'])).
% 0.90/1.08  thf('53', plain,
% 0.90/1.08      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['38', '39'])).
% 0.90/1.08  thf(t94_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( k2_xboole_0 @ A @ B ) =
% 0.90/1.08       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.08  thf('54', plain,
% 0.90/1.08      (![X24 : $i, X25 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ X24 @ X25)
% 0.90/1.08           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 0.90/1.08              (k3_xboole_0 @ X24 @ X25)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.90/1.08  thf('55', plain,
% 0.90/1.08      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.08         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.90/1.08           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.90/1.08  thf('56', plain,
% 0.90/1.08      (![X24 : $i, X25 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ X24 @ X25)
% 0.90/1.08           = (k5_xboole_0 @ X24 @ 
% 0.90/1.08              (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X24 @ X25))))),
% 0.90/1.08      inference('demod', [status(thm)], ['54', '55'])).
% 0.90/1.08  thf('57', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.90/1.08           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['53', '56'])).
% 0.90/1.08  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['48', '49'])).
% 0.90/1.08  thf('59', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.90/1.08      inference('cnf', [status(esa)], [t5_boole])).
% 0.90/1.08  thf('60', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.90/1.08      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.90/1.08  thf('61', plain,
% 0.90/1.08      (![X24 : $i, X25 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ X24 @ X25)
% 0.90/1.08           = (k5_xboole_0 @ X24 @ 
% 0.90/1.08              (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X24 @ X25))))),
% 0.90/1.08      inference('demod', [status(thm)], ['54', '55'])).
% 0.90/1.08  thf('62', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.90/1.08           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['60', '61'])).
% 0.90/1.08  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['46', '47'])).
% 0.90/1.08  thf('64', plain,
% 0.90/1.08      (![X14 : $i, X15 : $i]:
% 0.90/1.08         ((k4_xboole_0 @ X14 @ X15)
% 0.90/1.08           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.08  thf('65', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.08      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.90/1.08  thf('66', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((X1) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['52', '65'])).
% 0.90/1.08  thf('67', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.90/1.08      inference('demod', [status(thm)], ['15', '16', '51', '66'])).
% 0.90/1.08  thf('68', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k4_xboole_0 @ X0 @ X1)
% 0.90/1.08           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['5', '67'])).
% 0.90/1.08  thf('69', plain,
% 0.90/1.08      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.90/1.08         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['4', '68'])).
% 0.90/1.08  thf('70', plain,
% 0.90/1.08      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X7 @ X8)
% 0.90/1.08          | ~ (r2_hidden @ X7 @ X9)
% 0.90/1.08          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.90/1.08  thf('71', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X0 @ 
% 0.90/1.08             (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.90/1.08          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.90/1.08          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['69', '70'])).
% 0.90/1.08  thf(d1_enumset1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.08     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.90/1.08       ( ![E:$i]:
% 0.90/1.08         ( ( r2_hidden @ E @ D ) <=>
% 0.90/1.08           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.90/1.08  thf(zf_stmt_1, axiom,
% 0.90/1.08    (![E:$i,C:$i,B:$i,A:$i]:
% 0.90/1.08     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.90/1.08       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.90/1.08  thf('72', plain,
% 0.90/1.08      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.90/1.08         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 0.90/1.08          | ((X29) = (X30))
% 0.90/1.08          | ((X29) = (X31))
% 0.90/1.08          | ((X29) = (X32)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.08  thf('73', plain,
% 0.90/1.08      (![X3 : $i, X5 : $i]:
% 0.90/1.08         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('74', plain,
% 0.90/1.08      (![X40 : $i, X42 : $i, X43 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X43 @ X42)
% 0.90/1.08          | ((X43) = (X40))
% 0.90/1.08          | ((X42) != (k1_tarski @ X40)))),
% 0.90/1.08      inference('cnf', [status(esa)], [d1_tarski])).
% 0.90/1.08  thf('75', plain,
% 0.90/1.08      (![X40 : $i, X43 : $i]:
% 0.90/1.08         (((X43) = (X40)) | ~ (r2_hidden @ X43 @ (k1_tarski @ X40)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['74'])).
% 0.90/1.08  thf('76', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.90/1.08          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['73', '75'])).
% 0.90/1.08  thf('77', plain,
% 0.90/1.08      (![X3 : $i, X5 : $i]:
% 0.90/1.08         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('78', plain,
% 0.90/1.08      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.90/1.08         = (k1_tarski @ sk_A))),
% 0.90/1.08      inference('demod', [status(thm)], ['2', '3'])).
% 0.90/1.08  thf('79', plain,
% 0.90/1.08      (![X26 : $i, X27 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ X26 @ X27)
% 0.90/1.08           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.90/1.08  thf('80', plain,
% 0.90/1.08      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.90/1.08         ((r2_hidden @ X7 @ X8)
% 0.90/1.08          | (r2_hidden @ X7 @ X9)
% 0.90/1.08          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.90/1.08  thf('81', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.90/1.08          | (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.90/1.08          | (r2_hidden @ X2 @ X1))),
% 0.90/1.08      inference('sup-', [status(thm)], ['79', '80'])).
% 0.90/1.08  thf('82', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.90/1.08          | (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.90/1.08          | (r2_hidden @ X0 @ 
% 0.90/1.08             (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['78', '81'])).
% 0.90/1.08  thf('83', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.90/1.08          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ 
% 0.90/1.08             (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.90/1.08          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ (k1_tarski @ sk_B)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['77', '82'])).
% 0.90/1.08  thf('84', plain,
% 0.90/1.08      (![X3 : $i, X5 : $i]:
% 0.90/1.08         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('85', plain,
% 0.90/1.08      (((r2_hidden @ 
% 0.90/1.08         (sk_C @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 0.90/1.08          (k1_tarski @ sk_A)) @ 
% 0.90/1.08         (k1_tarski @ sk_B))
% 0.90/1.08        | (r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.90/1.08           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.90/1.08        | (r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.90/1.08           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['83', '84'])).
% 0.90/1.08  thf('86', plain,
% 0.90/1.08      (((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.90/1.08         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.90/1.08        | (r2_hidden @ 
% 0.90/1.08           (sk_C @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 0.90/1.08            (k1_tarski @ sk_A)) @ 
% 0.90/1.08           (k1_tarski @ sk_B)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['85'])).
% 0.90/1.08  thf(t69_enumset1, axiom,
% 0.90/1.08    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.90/1.08  thf('87', plain,
% 0.90/1.08      (![X49 : $i]: ((k2_tarski @ X49 @ X49) = (k1_tarski @ X49))),
% 0.90/1.08      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.08  thf(t70_enumset1, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.90/1.08  thf('88', plain,
% 0.90/1.08      (![X50 : $i, X51 : $i]:
% 0.90/1.08         ((k1_enumset1 @ X50 @ X50 @ X51) = (k2_tarski @ X50 @ X51))),
% 0.90/1.08      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.90/1.08  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.90/1.08  thf(zf_stmt_3, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.08     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.90/1.08       ( ![E:$i]:
% 0.90/1.08         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.90/1.08  thf('89', plain,
% 0.90/1.08      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X38 @ X37)
% 0.90/1.08          | ~ (zip_tseitin_0 @ X38 @ X34 @ X35 @ X36)
% 0.90/1.08          | ((X37) != (k1_enumset1 @ X36 @ X35 @ X34)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.08  thf('90', plain,
% 0.90/1.08      (![X34 : $i, X35 : $i, X36 : $i, X38 : $i]:
% 0.90/1.08         (~ (zip_tseitin_0 @ X38 @ X34 @ X35 @ X36)
% 0.90/1.08          | ~ (r2_hidden @ X38 @ (k1_enumset1 @ X36 @ X35 @ X34)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['89'])).
% 0.90/1.08  thf('91', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.90/1.08          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.90/1.08      inference('sup-', [status(thm)], ['88', '90'])).
% 0.90/1.08  thf('92', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.90/1.08          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['87', '91'])).
% 0.90/1.08  thf('93', plain,
% 0.90/1.08      (((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.90/1.08         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.90/1.08        | ~ (zip_tseitin_0 @ 
% 0.90/1.08             (sk_C @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 0.90/1.08              (k1_tarski @ sk_A)) @ 
% 0.90/1.08             sk_B @ sk_B @ sk_B))),
% 0.90/1.08      inference('sup-', [status(thm)], ['86', '92'])).
% 0.90/1.08  thf('94', plain,
% 0.90/1.08      ((~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)
% 0.90/1.08        | (r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.90/1.08           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.90/1.08        | (r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.90/1.08           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['76', '93'])).
% 0.90/1.08  thf('95', plain,
% 0.90/1.08      (((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.90/1.08         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.90/1.08        | ~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B))),
% 0.90/1.08      inference('simplify', [status(thm)], ['94'])).
% 0.90/1.08  thf('96', plain,
% 0.90/1.08      ((((sk_A) = (sk_B))
% 0.90/1.08        | ((sk_A) = (sk_B))
% 0.90/1.08        | ((sk_A) = (sk_B))
% 0.90/1.08        | (r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.90/1.08           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['72', '95'])).
% 0.90/1.08  thf('97', plain,
% 0.90/1.08      (((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.90/1.08         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.90/1.08        | ((sk_A) = (sk_B)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['96'])).
% 0.90/1.08  thf('98', plain, (((sk_A) != (sk_B))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('99', plain,
% 0.90/1.08      ((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.90/1.08        (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.90/1.08      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 0.90/1.08  thf('100', plain,
% 0.90/1.08      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X2 @ X3)
% 0.90/1.08          | (r2_hidden @ X2 @ X4)
% 0.90/1.08          | ~ (r1_tarski @ X3 @ X4))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('101', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r2_hidden @ X0 @ 
% 0.90/1.08           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.90/1.08          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['99', '100'])).
% 0.90/1.08  thf('102', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.90/1.08          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.90/1.08      inference('clc', [status(thm)], ['71', '101'])).
% 0.90/1.08  thf('103', plain, (~ (r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['1', '102'])).
% 0.90/1.08  thf('104', plain,
% 0.90/1.08      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.90/1.08         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['4', '68'])).
% 0.90/1.08  thf('105', plain, (![X40 : $i]: (r2_hidden @ X40 @ (k1_tarski @ X40))),
% 0.90/1.08      inference('simplify', [status(thm)], ['0'])).
% 0.90/1.08  thf('106', plain,
% 0.90/1.08      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.90/1.08         ((r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X10))
% 0.90/1.08          | (r2_hidden @ X7 @ X10)
% 0.90/1.08          | ~ (r2_hidden @ X7 @ X8))),
% 0.90/1.08      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.90/1.08  thf('107', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((r2_hidden @ X0 @ X1)
% 0.90/1.08          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['105', '106'])).
% 0.90/1.08  thf('108', plain,
% 0.90/1.08      (((r2_hidden @ sk_B @ 
% 0.90/1.08         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.90/1.08        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['104', '107'])).
% 0.90/1.08  thf('109', plain, (~ (r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['1', '102'])).
% 0.90/1.08  thf('110', plain,
% 0.90/1.08      ((r2_hidden @ sk_B @ 
% 0.90/1.08        (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.90/1.08      inference('clc', [status(thm)], ['108', '109'])).
% 0.90/1.08  thf('111', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.90/1.08          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['73', '75'])).
% 0.90/1.08  thf('112', plain,
% 0.90/1.08      (![X3 : $i, X5 : $i]:
% 0.90/1.08         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('113', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X0 @ X1)
% 0.90/1.08          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.90/1.08          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.90/1.08      inference('sup-', [status(thm)], ['111', '112'])).
% 0.90/1.08  thf('114', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.90/1.08      inference('simplify', [status(thm)], ['113'])).
% 0.90/1.08  thf('115', plain,
% 0.90/1.08      ((r1_tarski @ (k1_tarski @ sk_B) @ 
% 0.90/1.08        (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['110', '114'])).
% 0.90/1.08  thf('116', plain,
% 0.90/1.08      (![X16 : $i, X17 : $i]:
% 0.90/1.08         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.90/1.08      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.90/1.08  thf('117', plain,
% 0.90/1.08      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.90/1.08         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.90/1.08         = (k1_tarski @ sk_B))),
% 0.90/1.08      inference('sup-', [status(thm)], ['115', '116'])).
% 0.90/1.08  thf('118', plain,
% 0.90/1.08      (![X24 : $i, X25 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ X24 @ X25)
% 0.90/1.08           = (k5_xboole_0 @ X24 @ 
% 0.90/1.08              (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X24 @ X25))))),
% 0.90/1.08      inference('demod', [status(thm)], ['54', '55'])).
% 0.90/1.08  thf('119', plain,
% 0.90/1.08      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.90/1.08         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.90/1.08         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.90/1.08            (k5_xboole_0 @ 
% 0.90/1.08             (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 0.90/1.08             (k1_tarski @ sk_B))))),
% 0.90/1.08      inference('sup+', [status(thm)], ['117', '118'])).
% 0.90/1.08  thf(t39_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.90/1.08  thf('120', plain,
% 0.90/1.08      (![X18 : $i, X19 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 0.90/1.08           = (k2_xboole_0 @ X18 @ X19))),
% 0.90/1.08      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.90/1.08  thf('121', plain,
% 0.90/1.08      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.90/1.08         = (k1_tarski @ sk_A))),
% 0.90/1.08      inference('demod', [status(thm)], ['2', '3'])).
% 0.90/1.08  thf('122', plain,
% 0.90/1.08      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.08         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.90/1.08           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.90/1.08  thf('123', plain,
% 0.90/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['9', '10'])).
% 0.90/1.08  thf('124', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.90/1.08           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.90/1.08      inference('sup+', [status(thm)], ['122', '123'])).
% 0.90/1.08  thf('125', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['27', '36'])).
% 0.90/1.08  thf('126', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k1_xboole_0)
% 0.90/1.08           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.90/1.08      inference('demod', [status(thm)], ['124', '125'])).
% 0.90/1.08  thf('127', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.90/1.08      inference('demod', [status(thm)], ['15', '16', '51', '66'])).
% 0.90/1.08  thf('128', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.90/1.08           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['126', '127'])).
% 0.90/1.08  thf('129', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.90/1.08      inference('cnf', [status(esa)], [t5_boole])).
% 0.90/1.08  thf('130', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.90/1.08      inference('demod', [status(thm)], ['128', '129'])).
% 0.90/1.08  thf('131', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.90/1.08      inference('demod', [status(thm)], ['15', '16', '51', '66'])).
% 0.90/1.08  thf('132', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['130', '131'])).
% 0.90/1.08  thf('133', plain,
% 0.90/1.08      (![X26 : $i, X27 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ X26 @ X27)
% 0.90/1.08           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.90/1.08  thf('134', plain,
% 0.90/1.08      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.90/1.08         = (k1_tarski @ sk_A))),
% 0.90/1.08      inference('demod', [status(thm)], ['2', '3'])).
% 0.90/1.08  thf('135', plain,
% 0.90/1.08      (((k1_tarski @ sk_A)
% 0.90/1.08         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.90/1.08      inference('demod', [status(thm)],
% 0.90/1.08                ['119', '120', '121', '132', '133', '134'])).
% 0.90/1.08  thf('136', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((r2_hidden @ X0 @ X1)
% 0.90/1.08          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['105', '106'])).
% 0.90/1.08  thf('137', plain,
% 0.90/1.08      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.90/1.08        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['135', '136'])).
% 0.90/1.08  thf('138', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.90/1.08      inference('simplify', [status(thm)], ['137'])).
% 0.90/1.08  thf('139', plain, ($false), inference('demod', [status(thm)], ['103', '138'])).
% 0.90/1.08  
% 0.90/1.08  % SZS output end Refutation
% 0.90/1.08  
% 0.90/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
