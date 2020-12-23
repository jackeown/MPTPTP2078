%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0kv2KBmatt

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:10 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  101 (1340 expanded)
%              Number of leaves         :   24 ( 411 expanded)
%              Depth                    :   25
%              Number of atoms          :  689 (10101 expanded)
%              Number of equality atoms :   74 ( 887 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('40',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','34'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('46',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','34'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','34'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['44','55','58'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('65',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','34'])).

thf('67',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('69',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('70',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('71',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('72',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38 = X37 )
      | ~ ( r1_tarski @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('73',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0kv2KBmatt
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:57:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.59/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.85  % Solved by: fo/fo7.sh
% 0.59/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.85  % done 820 iterations in 0.410s
% 0.59/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.85  % SZS output start Refutation
% 0.59/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.85  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.85  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.85  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.85  thf(t13_zfmisc_1, conjecture,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.59/0.85         ( k1_tarski @ A ) ) =>
% 0.59/0.85       ( ( A ) = ( B ) ) ))).
% 0.59/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.85    (~( ![A:$i,B:$i]:
% 0.59/0.85        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.59/0.85            ( k1_tarski @ A ) ) =>
% 0.59/0.85          ( ( A ) = ( B ) ) ) )),
% 0.59/0.85    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.59/0.85  thf('0', plain,
% 0.59/0.85      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.59/0.85         = (k1_tarski @ sk_A))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf(t98_xboole_1, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.59/0.85  thf('1', plain,
% 0.59/0.85      (![X25 : $i, X26 : $i]:
% 0.59/0.85         ((k2_xboole_0 @ X25 @ X26)
% 0.59/0.85           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.59/0.85  thf(d10_xboole_0, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.85  thf('2', plain,
% 0.59/0.85      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 0.59/0.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.85  thf('3', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.59/0.85      inference('simplify', [status(thm)], ['2'])).
% 0.59/0.85  thf(t28_xboole_1, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.85  thf('4', plain,
% 0.59/0.85      (![X16 : $i, X17 : $i]:
% 0.59/0.85         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.59/0.85      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.85  thf('5', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.85  thf(t100_xboole_1, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.85  thf('6', plain,
% 0.59/0.85      (![X14 : $i, X15 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X14 @ X15)
% 0.59/0.85           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.85  thf('7', plain,
% 0.59/0.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['5', '6'])).
% 0.59/0.85  thf(t91_xboole_1, axiom,
% 0.59/0.85    (![A:$i,B:$i,C:$i]:
% 0.59/0.85     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.85       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.59/0.85  thf('8', plain,
% 0.59/0.85      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.85         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.59/0.85           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.85  thf('9', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.59/0.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.59/0.85      inference('sup+', [status(thm)], ['7', '8'])).
% 0.59/0.85  thf(d3_tarski, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.85       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.85  thf('10', plain,
% 0.59/0.85      (![X3 : $i, X5 : $i]:
% 0.59/0.85         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.59/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.85  thf('11', plain,
% 0.59/0.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['5', '6'])).
% 0.59/0.85  thf(t1_xboole_0, axiom,
% 0.59/0.85    (![A:$i,B:$i,C:$i]:
% 0.59/0.85     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.59/0.85       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.59/0.85  thf('12', plain,
% 0.59/0.85      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.59/0.85         ((r2_hidden @ X7 @ X8)
% 0.59/0.85          | (r2_hidden @ X7 @ X9)
% 0.59/0.85          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.59/0.85  thf('13', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.59/0.85          | (r2_hidden @ X1 @ X0)
% 0.59/0.85          | (r2_hidden @ X1 @ X0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.85  thf('14', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.59/0.85      inference('simplify', [status(thm)], ['13'])).
% 0.59/0.85  thf('15', plain,
% 0.59/0.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['5', '6'])).
% 0.59/0.85  thf('16', plain,
% 0.59/0.85      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.59/0.85         (~ (r2_hidden @ X7 @ X8)
% 0.59/0.85          | ~ (r2_hidden @ X7 @ X9)
% 0.59/0.85          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.59/0.85  thf('17', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.59/0.85          | ~ (r2_hidden @ X1 @ X0)
% 0.59/0.85          | ~ (r2_hidden @ X1 @ X0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['15', '16'])).
% 0.59/0.85  thf('18', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (r2_hidden @ X1 @ X0)
% 0.59/0.85          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.59/0.85      inference('simplify', [status(thm)], ['17'])).
% 0.59/0.85  thf('19', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.59/0.85      inference('clc', [status(thm)], ['14', '18'])).
% 0.59/0.85  thf('20', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.59/0.85      inference('sup-', [status(thm)], ['10', '19'])).
% 0.59/0.85  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.59/0.85  thf('21', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 0.59/0.85      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.85  thf('22', plain,
% 0.59/0.85      (![X11 : $i, X13 : $i]:
% 0.59/0.85         (((X11) = (X13))
% 0.59/0.85          | ~ (r1_tarski @ X13 @ X11)
% 0.59/0.85          | ~ (r1_tarski @ X11 @ X13))),
% 0.59/0.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.85  thf('23', plain,
% 0.59/0.85      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['21', '22'])).
% 0.59/0.85  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['20', '23'])).
% 0.59/0.85  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['20', '23'])).
% 0.59/0.85  thf('26', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['24', '25'])).
% 0.59/0.85  thf('27', plain,
% 0.59/0.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['5', '6'])).
% 0.59/0.85  thf('28', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.59/0.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.59/0.85      inference('sup+', [status(thm)], ['7', '8'])).
% 0.59/0.85  thf('29', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.59/0.85           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.59/0.85      inference('sup+', [status(thm)], ['27', '28'])).
% 0.59/0.85  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['20', '23'])).
% 0.59/0.85  thf(t5_boole, axiom,
% 0.59/0.85    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.85  thf('31', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.59/0.85      inference('cnf', [status(esa)], [t5_boole])).
% 0.59/0.85  thf('32', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.59/0.85      inference('sup+', [status(thm)], ['30', '31'])).
% 0.59/0.85  thf('33', plain,
% 0.59/0.85      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.59/0.85      inference('demod', [status(thm)], ['29', '32'])).
% 0.59/0.85  thf('34', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.59/0.85      inference('sup+', [status(thm)], ['26', '33'])).
% 0.59/0.85  thf('35', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.59/0.85      inference('demod', [status(thm)], ['9', '34'])).
% 0.59/0.85  thf('36', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X0 @ X1)
% 0.59/0.85           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.85      inference('sup+', [status(thm)], ['1', '35'])).
% 0.59/0.85  thf('37', plain,
% 0.59/0.85      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.59/0.85         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.59/0.85      inference('sup+', [status(thm)], ['0', '36'])).
% 0.59/0.85  thf('38', plain,
% 0.59/0.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['5', '6'])).
% 0.59/0.85  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['20', '23'])).
% 0.59/0.85  thf('40', plain,
% 0.59/0.85      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.59/0.85      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.59/0.85  thf('41', plain,
% 0.59/0.85      (![X14 : $i, X15 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X14 @ X15)
% 0.59/0.85           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.85  thf('42', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.59/0.85      inference('demod', [status(thm)], ['9', '34'])).
% 0.59/0.85  thf('43', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((k3_xboole_0 @ X1 @ X0)
% 0.59/0.85           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.85      inference('sup+', [status(thm)], ['41', '42'])).
% 0.59/0.85  thf('44', plain,
% 0.59/0.85      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.59/0.85         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['40', '43'])).
% 0.59/0.85  thf('45', plain,
% 0.59/0.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['5', '6'])).
% 0.59/0.85  thf('46', plain,
% 0.59/0.85      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.85         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.59/0.85           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.85  thf('47', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.59/0.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.59/0.85      inference('sup+', [status(thm)], ['45', '46'])).
% 0.59/0.85  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['20', '23'])).
% 0.59/0.85  thf('49', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((k1_xboole_0)
% 0.59/0.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.59/0.85      inference('demod', [status(thm)], ['47', '48'])).
% 0.59/0.85  thf('50', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.59/0.85      inference('demod', [status(thm)], ['9', '34'])).
% 0.59/0.85  thf('51', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.59/0.85           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['49', '50'])).
% 0.59/0.85  thf('52', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.59/0.85      inference('cnf', [status(esa)], [t5_boole])).
% 0.59/0.85  thf('53', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.59/0.85      inference('demod', [status(thm)], ['51', '52'])).
% 0.59/0.85  thf('54', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.59/0.85      inference('demod', [status(thm)], ['9', '34'])).
% 0.59/0.85  thf('55', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['53', '54'])).
% 0.59/0.85  thf('56', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['20', '23'])).
% 0.59/0.85  thf('57', plain,
% 0.59/0.85      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.59/0.85      inference('demod', [status(thm)], ['29', '32'])).
% 0.59/0.85  thf('58', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['56', '57'])).
% 0.59/0.85  thf('59', plain,
% 0.59/0.85      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.59/0.85         = (k1_tarski @ sk_B))),
% 0.59/0.85      inference('demod', [status(thm)], ['44', '55', '58'])).
% 0.59/0.85  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.85    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.85  thf('60', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.85  thf('61', plain,
% 0.59/0.85      (![X14 : $i, X15 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X14 @ X15)
% 0.59/0.85           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.85  thf('62', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X0 @ X1)
% 0.59/0.85           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.85      inference('sup+', [status(thm)], ['60', '61'])).
% 0.59/0.85  thf('63', plain,
% 0.59/0.85      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.59/0.85         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.59/0.85      inference('sup+', [status(thm)], ['59', '62'])).
% 0.59/0.85  thf('64', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['53', '54'])).
% 0.59/0.85  thf('65', plain,
% 0.59/0.85      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.59/0.85         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.59/0.85      inference('demod', [status(thm)], ['63', '64'])).
% 0.59/0.85  thf('66', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.59/0.85      inference('demod', [status(thm)], ['9', '34'])).
% 0.59/0.85  thf('67', plain,
% 0.59/0.85      (((k1_tarski @ sk_A)
% 0.59/0.85         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.59/0.85            (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 0.59/0.85      inference('sup+', [status(thm)], ['65', '66'])).
% 0.59/0.85  thf('68', plain,
% 0.59/0.85      (![X25 : $i, X26 : $i]:
% 0.59/0.85         ((k2_xboole_0 @ X25 @ X26)
% 0.59/0.85           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.59/0.85  thf('69', plain,
% 0.59/0.85      (((k1_tarski @ sk_A)
% 0.59/0.85         = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.59/0.85      inference('demod', [status(thm)], ['67', '68'])).
% 0.59/0.85  thf(t7_xboole_1, axiom,
% 0.59/0.85    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.85  thf('70', plain,
% 0.59/0.85      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.59/0.85      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.59/0.85  thf('71', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 0.59/0.85      inference('sup+', [status(thm)], ['69', '70'])).
% 0.59/0.85  thf(t6_zfmisc_1, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.59/0.85       ( ( A ) = ( B ) ) ))).
% 0.59/0.85  thf('72', plain,
% 0.59/0.85      (![X37 : $i, X38 : $i]:
% 0.59/0.85         (((X38) = (X37))
% 0.59/0.85          | ~ (r1_tarski @ (k1_tarski @ X38) @ (k1_tarski @ X37)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.59/0.85  thf('73', plain, (((sk_B) = (sk_A))),
% 0.59/0.85      inference('sup-', [status(thm)], ['71', '72'])).
% 0.59/0.85  thf('74', plain, (((sk_A) != (sk_B))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('75', plain, ($false),
% 0.59/0.85      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.59/0.85  
% 0.59/0.85  % SZS output end Refutation
% 0.59/0.85  
% 0.59/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
