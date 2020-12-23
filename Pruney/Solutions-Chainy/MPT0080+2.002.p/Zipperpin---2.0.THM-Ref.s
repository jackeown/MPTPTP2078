%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hWKObyrJIQ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:04 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 410 expanded)
%              Number of leaves         :   24 ( 141 expanded)
%              Depth                    :   19
%              Number of atoms          :  908 (3237 expanded)
%              Number of equality atoms :   94 ( 307 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X19: $i] :
      ( ( k2_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['11','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X19: $i] :
      ( ( k2_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('34',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','34'])).

thf('36',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['18','35'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('43',plain,
    ( sk_C_1
    = ( k2_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['54','64'])).

thf('66',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['48','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('68',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('70',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_C_1 )
    = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('76',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['54','64'])).

thf('80',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('85',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('89',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['80','86','87','88'])).

thf('90',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['43','91'])).

thf('93',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('94',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('95',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['80','86','87','88'])).

thf('96',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['0','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hWKObyrJIQ
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:32:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.76/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.96  % Solved by: fo/fo7.sh
% 0.76/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.96  % done 1311 iterations in 0.513s
% 0.76/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.96  % SZS output start Refutation
% 0.76/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.96  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.76/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.96  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/0.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.76/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.96  thf(t73_xboole_1, conjecture,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.76/0.96       ( r1_tarski @ A @ B ) ))).
% 0.76/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.96    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.96        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.76/0.96            ( r1_xboole_0 @ A @ C ) ) =>
% 0.76/0.96          ( r1_tarski @ A @ B ) ) )),
% 0.76/0.96    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.76/0.96  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('1', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(t12_xboole_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.76/0.96  thf('2', plain,
% 0.76/0.96      (![X17 : $i, X18 : $i]:
% 0.76/0.96         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 0.76/0.96      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.96  thf('3', plain,
% 0.76/0.96      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 0.76/0.96         = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.76/0.96      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.96  thf(t40_xboole_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.76/0.96  thf('4', plain,
% 0.76/0.96      (![X23 : $i, X24 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24)
% 0.76/0.96           = (k4_xboole_0 @ X23 @ X24))),
% 0.76/0.96      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.76/0.96  thf('5', plain,
% 0.76/0.96      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ 
% 0.76/0.96         (k2_xboole_0 @ sk_B @ sk_C_1))
% 0.76/0.96         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['3', '4'])).
% 0.76/0.96  thf(commutativity_k2_xboole_0, axiom,
% 0.76/0.96    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.76/0.96  thf('6', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.96  thf(t1_boole, axiom,
% 0.76/0.96    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.76/0.96  thf('7', plain, (![X19 : $i]: ((k2_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.76/0.96      inference('cnf', [status(esa)], [t1_boole])).
% 0.76/0.96  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['6', '7'])).
% 0.76/0.96  thf('9', plain,
% 0.76/0.96      (![X23 : $i, X24 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24)
% 0.76/0.96           = (k4_xboole_0 @ X23 @ X24))),
% 0.76/0.96      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.76/0.96  thf('10', plain,
% 0.76/0.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['8', '9'])).
% 0.76/0.96  thf('11', plain,
% 0.76/0.96      (((k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 0.76/0.96         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.76/0.96      inference('demod', [status(thm)], ['5', '10'])).
% 0.76/0.96  thf(t3_boole, axiom,
% 0.76/0.96    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.76/0.96  thf('12', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.76/0.96      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.96  thf(t48_xboole_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/0.96  thf('13', plain,
% 0.76/0.96      (![X28 : $i, X29 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 0.76/0.96           = (k3_xboole_0 @ X28 @ X29))),
% 0.76/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.96  thf('14', plain,
% 0.76/0.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['12', '13'])).
% 0.76/0.96  thf('15', plain,
% 0.76/0.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['8', '9'])).
% 0.76/0.96  thf('16', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['14', '15'])).
% 0.76/0.96  thf(commutativity_k3_xboole_0, axiom,
% 0.76/0.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.76/0.96  thf('17', plain,
% 0.76/0.96      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.96  thf('18', plain,
% 0.76/0.96      (((k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 0.76/0.96         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.76/0.96      inference('demod', [status(thm)], ['11', '16', '17'])).
% 0.76/0.96  thf('19', plain,
% 0.76/0.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['12', '13'])).
% 0.76/0.96  thf('20', plain,
% 0.76/0.96      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.96  thf('21', plain,
% 0.76/0.96      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['19', '20'])).
% 0.76/0.96  thf(d3_tarski, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( r1_tarski @ A @ B ) <=>
% 0.76/0.96       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.76/0.96  thf('22', plain,
% 0.76/0.96      (![X5 : $i, X7 : $i]:
% 0.76/0.96         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.96  thf('23', plain,
% 0.76/0.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['8', '9'])).
% 0.76/0.96  thf(d5_xboole_0, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.76/0.96       ( ![D:$i]:
% 0.76/0.96         ( ( r2_hidden @ D @ C ) <=>
% 0.76/0.96           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.76/0.96  thf('24', plain,
% 0.76/0.96      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X12 @ X11)
% 0.76/0.96          | ~ (r2_hidden @ X12 @ X10)
% 0.76/0.96          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.76/0.96      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.96  thf('25', plain,
% 0.76/0.96      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X12 @ X10)
% 0.76/0.96          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.76/0.96      inference('simplify', [status(thm)], ['24'])).
% 0.76/0.96  thf('26', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.76/0.96          | ~ (r2_hidden @ X1 @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['23', '25'])).
% 0.76/0.96  thf('27', plain,
% 0.76/0.96      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X12 @ X11)
% 0.76/0.96          | (r2_hidden @ X12 @ X9)
% 0.76/0.96          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.76/0.96      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.96  thf('28', plain,
% 0.76/0.96      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.76/0.96         ((r2_hidden @ X12 @ X9)
% 0.76/0.96          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.76/0.96      inference('simplify', [status(thm)], ['27'])).
% 0.76/0.96  thf('29', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.76/0.96      inference('clc', [status(thm)], ['26', '28'])).
% 0.76/0.96  thf('30', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.76/0.96      inference('sup-', [status(thm)], ['22', '29'])).
% 0.76/0.96  thf('31', plain,
% 0.76/0.96      (![X17 : $i, X18 : $i]:
% 0.76/0.96         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 0.76/0.96      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.96  thf('32', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['30', '31'])).
% 0.76/0.96  thf('33', plain, (![X19 : $i]: ((k2_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.76/0.96      inference('cnf', [status(esa)], [t1_boole])).
% 0.76/0.96  thf('34', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['32', '33'])).
% 0.76/0.96  thf('35', plain,
% 0.76/0.96      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.76/0.96      inference('demod', [status(thm)], ['21', '34'])).
% 0.76/0.96  thf('36', plain,
% 0.76/0.96      (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.76/0.96      inference('demod', [status(thm)], ['18', '35'])).
% 0.76/0.96  thf(t41_xboole_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.76/0.96       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.76/0.96  thf('37', plain,
% 0.76/0.96      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X27)
% 0.76/0.96           = (k4_xboole_0 @ X25 @ (k2_xboole_0 @ X26 @ X27)))),
% 0.76/0.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.96  thf(t39_xboole_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.76/0.96  thf('38', plain,
% 0.76/0.96      (![X20 : $i, X21 : $i]:
% 0.76/0.96         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 0.76/0.96           = (k2_xboole_0 @ X20 @ X21))),
% 0.76/0.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.76/0.96  thf('39', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.96         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.76/0.96           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['37', '38'])).
% 0.76/0.96  thf('40', plain,
% 0.76/0.96      (((k2_xboole_0 @ sk_C_1 @ k1_xboole_0)
% 0.76/0.96         = (k2_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['36', '39'])).
% 0.76/0.96  thf('41', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.96  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['6', '7'])).
% 0.76/0.96  thf('43', plain,
% 0.76/0.96      (((sk_C_1) = (k2_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.76/0.96  thf('44', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(d7_xboole_0, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.76/0.96       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.76/0.96  thf('45', plain,
% 0.76/0.96      (![X14 : $i, X15 : $i]:
% 0.76/0.96         (((k3_xboole_0 @ X14 @ X15) = (k1_xboole_0))
% 0.76/0.96          | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.76/0.96      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/0.96  thf('46', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['44', '45'])).
% 0.76/0.96  thf('47', plain,
% 0.76/0.96      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.96  thf('48', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.76/0.96      inference('demod', [status(thm)], ['46', '47'])).
% 0.76/0.96  thf('49', plain,
% 0.76/0.96      (![X28 : $i, X29 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 0.76/0.96           = (k3_xboole_0 @ X28 @ X29))),
% 0.76/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.96  thf('50', plain,
% 0.76/0.96      (![X20 : $i, X21 : $i]:
% 0.76/0.96         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 0.76/0.96           = (k2_xboole_0 @ X20 @ X21))),
% 0.76/0.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.76/0.96  thf('51', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.96           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.76/0.96      inference('sup+', [status(thm)], ['49', '50'])).
% 0.76/0.96  thf('52', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.96  thf('53', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.96  thf('54', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.96           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.76/0.96  thf('55', plain,
% 0.76/0.96      (![X5 : $i, X7 : $i]:
% 0.76/0.96         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.96  thf('56', plain,
% 0.76/0.96      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.76/0.96         ((r2_hidden @ X12 @ X9)
% 0.76/0.96          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.76/0.96      inference('simplify', [status(thm)], ['27'])).
% 0.76/0.96  thf('57', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.96         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.76/0.96          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.76/0.96      inference('sup-', [status(thm)], ['55', '56'])).
% 0.76/0.96  thf('58', plain,
% 0.76/0.96      (![X5 : $i, X7 : $i]:
% 0.76/0.96         ((r1_tarski @ X5 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X5) @ X7))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.96  thf('59', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.76/0.96          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['57', '58'])).
% 0.76/0.96  thf('60', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.76/0.96      inference('simplify', [status(thm)], ['59'])).
% 0.76/0.96  thf('61', plain,
% 0.76/0.96      (![X17 : $i, X18 : $i]:
% 0.76/0.96         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 0.76/0.96      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.96  thf('62', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['60', '61'])).
% 0.76/0.96  thf('63', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.96  thf('64', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.76/0.96      inference('demod', [status(thm)], ['62', '63'])).
% 0.76/0.96  thf('65', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.96           = (X1))),
% 0.76/0.96      inference('demod', [status(thm)], ['54', '64'])).
% 0.76/0.96  thf('66', plain,
% 0.76/0.96      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_A)) = (sk_C_1))),
% 0.76/0.96      inference('sup+', [status(thm)], ['48', '65'])).
% 0.76/0.96  thf('67', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['6', '7'])).
% 0.76/0.96  thf('68', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.76/0.96      inference('demod', [status(thm)], ['66', '67'])).
% 0.76/0.96  thf('69', plain,
% 0.76/0.96      (![X23 : $i, X24 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24)
% 0.76/0.96           = (k4_xboole_0 @ X23 @ X24))),
% 0.76/0.96      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.76/0.96  thf('70', plain,
% 0.76/0.96      (![X28 : $i, X29 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 0.76/0.96           = (k3_xboole_0 @ X28 @ X29))),
% 0.76/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.96  thf('71', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.96           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['69', '70'])).
% 0.76/0.96  thf('72', plain,
% 0.76/0.96      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.96  thf('73', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.96           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['71', '72'])).
% 0.76/0.96  thf('74', plain,
% 0.76/0.96      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_C_1)
% 0.76/0.96         = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['68', '73'])).
% 0.76/0.96  thf('75', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.96  thf('76', plain,
% 0.76/0.96      (![X23 : $i, X24 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24)
% 0.76/0.96           = (k4_xboole_0 @ X23 @ X24))),
% 0.76/0.96      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.76/0.96  thf('77', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.76/0.96           = (k4_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('sup+', [status(thm)], ['75', '76'])).
% 0.76/0.96  thf('78', plain,
% 0.76/0.96      (((k4_xboole_0 @ sk_A @ sk_C_1)
% 0.76/0.96         = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.76/0.96      inference('demod', [status(thm)], ['74', '77'])).
% 0.76/0.96  thf('79', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.96           = (X1))),
% 0.76/0.96      inference('demod', [status(thm)], ['54', '64'])).
% 0.76/0.96  thf('80', plain,
% 0.76/0.96      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.76/0.96         (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_A))) = (sk_A))),
% 0.76/0.96      inference('sup+', [status(thm)], ['78', '79'])).
% 0.76/0.96  thf('81', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.76/0.96      inference('demod', [status(thm)], ['62', '63'])).
% 0.76/0.96  thf('82', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.76/0.96           = (k4_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('sup+', [status(thm)], ['75', '76'])).
% 0.76/0.96  thf('83', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ X0 @ X0)
% 0.76/0.96           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['81', '82'])).
% 0.76/0.96  thf('84', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['32', '33'])).
% 0.76/0.96  thf('85', plain,
% 0.76/0.96      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X27)
% 0.76/0.96           = (k4_xboole_0 @ X25 @ (k2_xboole_0 @ X26 @ X27)))),
% 0.76/0.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.96  thf('86', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.76/0.96  thf('87', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.96  thf('88', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.96      inference('sup+', [status(thm)], ['6', '7'])).
% 0.76/0.96  thf('89', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['80', '86', '87', '88'])).
% 0.76/0.96  thf('90', plain,
% 0.76/0.96      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X27)
% 0.76/0.96           = (k4_xboole_0 @ X25 @ (k2_xboole_0 @ X26 @ X27)))),
% 0.76/0.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.96  thf('91', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ sk_A @ X0)
% 0.76/0.96           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['89', '90'])).
% 0.76/0.96  thf('92', plain,
% 0.76/0.96      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.76/0.96         = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.76/0.96      inference('sup+', [status(thm)], ['43', '91'])).
% 0.76/0.96  thf('93', plain,
% 0.76/0.96      (![X28 : $i, X29 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 0.76/0.96           = (k3_xboole_0 @ X28 @ X29))),
% 0.76/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.96  thf('94', plain,
% 0.76/0.96      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.96  thf('95', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['80', '86', '87', '88'])).
% 0.76/0.96  thf('96', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.76/0.96  thf('97', plain,
% 0.76/0.96      (![X28 : $i, X29 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 0.76/0.96           = (k3_xboole_0 @ X28 @ X29))),
% 0.76/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.96  thf('98', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.76/0.96      inference('simplify', [status(thm)], ['59'])).
% 0.76/0.96  thf('99', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.76/0.96      inference('sup+', [status(thm)], ['97', '98'])).
% 0.76/0.96  thf('100', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.76/0.96      inference('sup+', [status(thm)], ['96', '99'])).
% 0.76/0.96  thf('101', plain, ($false), inference('demod', [status(thm)], ['0', '100'])).
% 0.76/0.96  
% 0.76/0.96  % SZS output end Refutation
% 0.76/0.96  
% 0.76/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
