%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QaKDtnXvBo

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:15 EST 2020

% Result     : Theorem 5.14s
% Output     : Refutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :  306 (4349 expanded)
%              Number of leaves         :   31 (1307 expanded)
%              Depth                    :   45
%              Number of atoms          : 2862 (37659 expanded)
%              Number of equality atoms :  252 (3122 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ( X18 != X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X19: $i] :
      ( r1_tarski @ X19 @ X19 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k4_xboole_0 @ X47 @ ( k1_tarski @ X48 ) )
        = X47 )
      | ( r2_hidden @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X25: $i] :
      ( r1_tarski @ k1_xboole_0 @ X25 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    ! [X18: $i,X20: $i] :
      ( ( X18 = X20 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','27'])).

thf('29',plain,(
    ! [X25: $i] :
      ( r1_tarski @ k1_xboole_0 @ X25 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ( r2_hidden @ X12 @ X15 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('38',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      | ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
      | ( r2_hidden @ sk_A @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('44',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('45',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X46 @ X47 )
      | ( ( k4_xboole_0 @ X47 @ ( k1_tarski @ X46 ) )
       != X47 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
       != X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['40','48'])).

thf('50',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('52',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('56',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('57',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) @ X1 )
        | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( sk_C @ X1 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) @ sk_B )
        | ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) @ X1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 )
        | ( r1_tarski @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
        | ( r1_tarski @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('70',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','72'])).

thf('74',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','73'])).

thf('75',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

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

thf('76',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( X29 = X30 )
      | ( X29 = X31 )
      | ( X29 = X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('77',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('79',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
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

thf('80',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X38 @ X37 )
      | ~ ( zip_tseitin_0 @ X38 @ X34 @ X35 @ X36 )
      | ( X37
       != ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('81',plain,(
    ! [X34: $i,X35: $i,X36: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X34 @ X35 @ X36 )
      | ~ ( r2_hidden @ X38 @ ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['75','89'])).

thf('91',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('92',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('94',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('96',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('98',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X18: $i,X20: $i] :
      ( ( X18 = X20 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('100',plain,
    ( ( ~ ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ( sk_B
        = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('102',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X46 @ X47 )
      | ( ( k4_xboole_0 @ X47 @ ( k1_tarski @ X46 ) )
       != X47 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('103',plain,
    ( ( ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
       != sk_B )
      | ~ ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('105',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
     != sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['100','105'])).

thf('107',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','106'])).

thf('108',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k4_xboole_0 @ X47 @ ( k1_tarski @ X48 ) )
        = X47 )
      | ( r2_hidden @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('109',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','73'])).

thf('110',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('111',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('113',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ sk_A ) @ X0 ) @ X1 )
        | ( X1
          = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
        | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ sk_A ) @ X0 ) @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 )
        | ( X0
          = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
        | ( X0
          = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
        | ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('116',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( X0 = k1_xboole_0 )
        | ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ( X0 = k1_xboole_0 )
        | ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ sk_B ) @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['109','118'])).

thf('120',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k4_xboole_0 @ X47 @ ( k1_tarski @ X48 ) )
        = X47 )
      | ( r2_hidden @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('122',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('132',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','136'])).

thf('138',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
          = k1_xboole_0 )
        | ( r2_hidden @ X1 @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['130','133'])).

thf('142',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
          = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        | ( r2_hidden @ X0 @ X1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('144',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k5_xboole_0 @ X1 @ k1_xboole_0 )
          = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        | ( r2_hidden @ X0 @ X1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
          = X0 )
        | ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ X1 @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['108','144'])).

thf('146',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X1 @ X0 )
        | ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
          = X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['40','48'])).

thf('148',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','73'])).

thf('149',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X46 @ X47 )
      | ( ( k4_xboole_0 @ X47 @ ( k1_tarski @ X46 ) )
       != X47 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('150',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('152',plain,
    ( ! [X0: $i] :
        ( ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
     != ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,
    ( ! [X0: $i] :
        ( ( ( k5_xboole_0 @ sk_B @ k1_xboole_0 )
         != ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
        | ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['146','153'])).

thf('155',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('157',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ X0 @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['107','157'])).

thf('159',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('160',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','158','159'])).

thf('161',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','160'])).

thf('162',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k4_xboole_0 @ X47 @ ( k1_tarski @ X48 ) )
        = X47 )
      | ( r2_hidden @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('163',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('164',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['167','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('173',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','21'])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X2 )
      | ( X2
        = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X2 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['175','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['130','133'])).

thf('181',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k4_xboole_0 @ X47 @ ( k1_tarski @ X48 ) )
        = X47 )
      | ( r2_hidden @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['181','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('190',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('195',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( ( k4_xboole_0 @ X2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['188','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('198',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('199',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','158'])).

thf('200',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['198','199'])).

thf('201',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['197','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['196','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['180','202'])).

thf('204',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('205',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('212',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ sk_B )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['203','212'])).

thf('214',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['179','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ sk_B )
        = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ k1_xboole_0 ) )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['172','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('219',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('220',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['217','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B ) @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_B )
      | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['171','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('225',plain,(
    ! [X18: $i,X20: $i] :
      ( ( X18 = X20 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['223','226'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_B )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['222','227'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_B )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( k5_xboole_0 @ X1 @ X1 ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['162','228'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( k5_xboole_0 @ X1 @ X1 ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('241',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ sk_B ) )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['230','241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('246',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('247',plain,(
    ! [X18: $i,X20: $i] :
      ( ( X18 = X20 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['245','248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('253',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('254',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      | ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('255',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ k1_xboole_0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['252','255'])).

thf('257',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('260',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['260'])).

thf('262',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['251','261'])).

thf('263',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['244','262'])).

thf('264',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['243','263'])).

thf('265',plain,(
    ! [X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ sk_B ) )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['242','264'])).

thf('266',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','160'])).

thf('267',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['267'])).

thf('269',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['198','199'])).

thf('270',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['268','269'])).

thf('271',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['244','262'])).

thf('272',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['161','270','271'])).

thf('273',plain,(
    $false ),
    inference(simplify,[status(thm)],['272'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QaKDtnXvBo
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.14/5.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.14/5.36  % Solved by: fo/fo7.sh
% 5.14/5.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.14/5.36  % done 6882 iterations in 4.905s
% 5.14/5.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.14/5.36  % SZS output start Refutation
% 5.14/5.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.14/5.36  thf(sk_A_type, type, sk_A: $i).
% 5.14/5.36  thf(sk_B_type, type, sk_B: $i).
% 5.14/5.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.14/5.36  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.14/5.36  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.14/5.36  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.14/5.36  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.14/5.36  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.14/5.36  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.14/5.36  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 5.14/5.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.14/5.36  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.14/5.36  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 5.14/5.36  thf(t67_zfmisc_1, conjecture,
% 5.14/5.36    (![A:$i,B:$i]:
% 5.14/5.36     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 5.14/5.36       ( ~( r2_hidden @ A @ B ) ) ))).
% 5.14/5.36  thf(zf_stmt_0, negated_conjecture,
% 5.14/5.36    (~( ![A:$i,B:$i]:
% 5.14/5.36        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 5.14/5.36          ( ~( r2_hidden @ A @ B ) ) ) )),
% 5.14/5.36    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 5.14/5.36  thf('0', plain,
% 5.14/5.36      (((r2_hidden @ sk_A @ sk_B)
% 5.14/5.36        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 5.14/5.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.36  thf('1', plain,
% 5.14/5.36      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 5.14/5.36         <= (~
% 5.14/5.36             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.36      inference('split', [status(esa)], ['0'])).
% 5.14/5.36  thf('2', plain,
% 5.14/5.36      ((~ (r2_hidden @ sk_A @ sk_B)
% 5.14/5.36        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 5.14/5.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.14/5.36  thf('3', plain,
% 5.14/5.36      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 5.14/5.36       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 5.14/5.36      inference('split', [status(esa)], ['2'])).
% 5.14/5.36  thf(d10_xboole_0, axiom,
% 5.14/5.36    (![A:$i,B:$i]:
% 5.14/5.36     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.14/5.36  thf('4', plain,
% 5.14/5.36      (![X18 : $i, X19 : $i]: ((r1_tarski @ X18 @ X19) | ((X18) != (X19)))),
% 5.14/5.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.14/5.36  thf('5', plain, (![X19 : $i]: (r1_tarski @ X19 @ X19)),
% 5.14/5.36      inference('simplify', [status(thm)], ['4'])).
% 5.14/5.36  thf(t28_xboole_1, axiom,
% 5.14/5.36    (![A:$i,B:$i]:
% 5.14/5.36     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.14/5.36  thf('6', plain,
% 5.14/5.36      (![X23 : $i, X24 : $i]:
% 5.14/5.36         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 5.14/5.36      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.14/5.36  thf('7', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 5.14/5.36      inference('sup-', [status(thm)], ['5', '6'])).
% 5.14/5.36  thf(t100_xboole_1, axiom,
% 5.14/5.36    (![A:$i,B:$i]:
% 5.14/5.36     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.14/5.36  thf('8', plain,
% 5.14/5.36      (![X21 : $i, X22 : $i]:
% 5.14/5.36         ((k4_xboole_0 @ X21 @ X22)
% 5.14/5.36           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 5.14/5.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.14/5.36  thf('9', plain,
% 5.14/5.36      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.14/5.36      inference('sup+', [status(thm)], ['7', '8'])).
% 5.14/5.36  thf(t65_zfmisc_1, axiom,
% 5.14/5.36    (![A:$i,B:$i]:
% 5.14/5.36     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 5.14/5.36       ( ~( r2_hidden @ B @ A ) ) ))).
% 5.14/5.36  thf('10', plain,
% 5.14/5.36      (![X47 : $i, X48 : $i]:
% 5.14/5.36         (((k4_xboole_0 @ X47 @ (k1_tarski @ X48)) = (X47))
% 5.14/5.36          | (r2_hidden @ X48 @ X47))),
% 5.14/5.36      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 5.14/5.36  thf('11', plain,
% 5.14/5.36      (![X0 : $i]:
% 5.14/5.36         (((k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 5.14/5.36            = (k1_tarski @ X0))
% 5.14/5.36          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 5.14/5.36      inference('sup+', [status(thm)], ['9', '10'])).
% 5.14/5.36  thf(d3_tarski, axiom,
% 5.14/5.36    (![A:$i,B:$i]:
% 5.14/5.36     ( ( r1_tarski @ A @ B ) <=>
% 5.14/5.36       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.14/5.36  thf('12', plain,
% 5.14/5.36      (![X3 : $i, X5 : $i]:
% 5.14/5.36         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 5.14/5.36      inference('cnf', [status(esa)], [d3_tarski])).
% 5.14/5.36  thf('13', plain,
% 5.14/5.36      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.14/5.36      inference('sup+', [status(thm)], ['7', '8'])).
% 5.14/5.36  thf(t36_xboole_1, axiom,
% 5.14/5.36    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 5.14/5.36  thf('14', plain,
% 5.14/5.36      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 5.14/5.36      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.14/5.36  thf('15', plain,
% 5.14/5.36      (![X2 : $i, X3 : $i, X4 : $i]:
% 5.14/5.36         (~ (r2_hidden @ X2 @ X3)
% 5.14/5.36          | (r2_hidden @ X2 @ X4)
% 5.14/5.36          | ~ (r1_tarski @ X3 @ X4))),
% 5.14/5.36      inference('cnf', [status(esa)], [d3_tarski])).
% 5.14/5.36  thf('16', plain,
% 5.14/5.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.36         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 5.14/5.36      inference('sup-', [status(thm)], ['14', '15'])).
% 5.14/5.36  thf('17', plain,
% 5.14/5.36      (![X0 : $i, X1 : $i]:
% 5.14/5.36         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 5.14/5.36      inference('sup-', [status(thm)], ['13', '16'])).
% 5.14/5.36  thf('18', plain,
% 5.14/5.36      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.14/5.36      inference('sup+', [status(thm)], ['7', '8'])).
% 5.14/5.36  thf(d5_xboole_0, axiom,
% 5.14/5.36    (![A:$i,B:$i,C:$i]:
% 5.14/5.36     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 5.14/5.36       ( ![D:$i]:
% 5.14/5.36         ( ( r2_hidden @ D @ C ) <=>
% 5.14/5.36           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 5.14/5.36  thf('19', plain,
% 5.14/5.36      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 5.14/5.36         (~ (r2_hidden @ X16 @ X15)
% 5.14/5.36          | ~ (r2_hidden @ X16 @ X14)
% 5.14/5.36          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 5.14/5.36      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.14/5.36  thf('20', plain,
% 5.14/5.36      (![X13 : $i, X14 : $i, X16 : $i]:
% 5.14/5.36         (~ (r2_hidden @ X16 @ X14)
% 5.14/5.36          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 5.14/5.36      inference('simplify', [status(thm)], ['19'])).
% 5.14/5.36  thf('21', plain,
% 5.14/5.36      (![X0 : $i, X1 : $i]:
% 5.14/5.36         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 5.14/5.36          | ~ (r2_hidden @ X1 @ X0))),
% 5.14/5.36      inference('sup-', [status(thm)], ['18', '20'])).
% 5.14/5.36  thf('22', plain,
% 5.14/5.36      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 5.14/5.36      inference('clc', [status(thm)], ['17', '21'])).
% 5.14/5.36  thf('23', plain,
% 5.14/5.36      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 5.14/5.36      inference('sup-', [status(thm)], ['12', '22'])).
% 5.14/5.36  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.14/5.36  thf('24', plain, (![X25 : $i]: (r1_tarski @ k1_xboole_0 @ X25)),
% 5.14/5.36      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.14/5.36  thf('25', plain,
% 5.14/5.36      (![X18 : $i, X20 : $i]:
% 5.14/5.36         (((X18) = (X20))
% 5.14/5.36          | ~ (r1_tarski @ X20 @ X18)
% 5.14/5.36          | ~ (r1_tarski @ X18 @ X20))),
% 5.14/5.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.14/5.36  thf('26', plain,
% 5.14/5.36      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.14/5.36      inference('sup-', [status(thm)], ['24', '25'])).
% 5.14/5.36  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.14/5.36      inference('sup-', [status(thm)], ['23', '26'])).
% 5.14/5.36  thf('28', plain,
% 5.14/5.36      (![X0 : $i]:
% 5.14/5.36         (((k1_xboole_0) = (k1_tarski @ X0))
% 5.14/5.36          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 5.14/5.36      inference('demod', [status(thm)], ['11', '27'])).
% 5.14/5.36  thf('29', plain, (![X25 : $i]: (r1_tarski @ k1_xboole_0 @ X25)),
% 5.14/5.36      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.14/5.36  thf('30', plain,
% 5.14/5.36      (![X23 : $i, X24 : $i]:
% 5.14/5.36         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 5.14/5.36      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.14/5.36  thf('31', plain,
% 5.14/5.36      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.14/5.36      inference('sup-', [status(thm)], ['29', '30'])).
% 5.14/5.36  thf(commutativity_k3_xboole_0, axiom,
% 5.14/5.36    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.14/5.36  thf('32', plain,
% 5.14/5.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.14/5.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.14/5.36  thf('33', plain,
% 5.14/5.36      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 5.14/5.36      inference('sup+', [status(thm)], ['31', '32'])).
% 5.14/5.36  thf('34', plain,
% 5.14/5.36      (![X21 : $i, X22 : $i]:
% 5.14/5.36         ((k4_xboole_0 @ X21 @ X22)
% 5.14/5.36           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 5.14/5.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.14/5.36  thf('35', plain,
% 5.14/5.36      (![X0 : $i]:
% 5.14/5.36         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.14/5.36      inference('sup+', [status(thm)], ['33', '34'])).
% 5.14/5.36  thf('36', plain,
% 5.14/5.36      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.36      inference('split', [status(esa)], ['0'])).
% 5.14/5.36  thf('37', plain,
% 5.14/5.36      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.14/5.36         (~ (r2_hidden @ X12 @ X13)
% 5.14/5.36          | (r2_hidden @ X12 @ X14)
% 5.14/5.36          | (r2_hidden @ X12 @ X15)
% 5.14/5.36          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 5.14/5.36      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.14/5.36  thf('38', plain,
% 5.14/5.36      (![X12 : $i, X13 : $i, X14 : $i]:
% 5.14/5.36         ((r2_hidden @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 5.14/5.36          | (r2_hidden @ X12 @ X14)
% 5.14/5.36          | ~ (r2_hidden @ X12 @ X13))),
% 5.14/5.36      inference('simplify', [status(thm)], ['37'])).
% 5.14/5.36  thf('39', plain,
% 5.14/5.36      ((![X0 : $i]:
% 5.14/5.36          ((r2_hidden @ sk_A @ X0)
% 5.14/5.36           | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))
% 5.14/5.36         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.36      inference('sup-', [status(thm)], ['36', '38'])).
% 5.14/5.36  thf('40', plain,
% 5.14/5.36      ((((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 5.14/5.36         | (r2_hidden @ sk_A @ k1_xboole_0))) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.36      inference('sup+', [status(thm)], ['35', '39'])).
% 5.14/5.36  thf('41', plain,
% 5.14/5.36      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 5.14/5.36      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.14/5.36  thf('42', plain,
% 5.14/5.36      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.14/5.36      inference('sup-', [status(thm)], ['24', '25'])).
% 5.14/5.36  thf('43', plain,
% 5.14/5.36      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.14/5.36      inference('sup-', [status(thm)], ['41', '42'])).
% 5.14/5.36  thf(t69_enumset1, axiom,
% 5.14/5.36    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.14/5.36  thf('44', plain,
% 5.14/5.36      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 5.14/5.36      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.14/5.36  thf('45', plain,
% 5.14/5.36      (![X46 : $i, X47 : $i]:
% 5.14/5.36         (~ (r2_hidden @ X46 @ X47)
% 5.14/5.36          | ((k4_xboole_0 @ X47 @ (k1_tarski @ X46)) != (X47)))),
% 5.14/5.36      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 5.14/5.36  thf('46', plain,
% 5.14/5.36      (![X0 : $i, X1 : $i]:
% 5.14/5.36         (((k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) != (X1))
% 5.14/5.36          | ~ (r2_hidden @ X0 @ X1))),
% 5.14/5.36      inference('sup-', [status(thm)], ['44', '45'])).
% 5.14/5.36  thf('47', plain,
% 5.14/5.36      (![X0 : $i]:
% 5.14/5.36         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 5.14/5.36      inference('sup-', [status(thm)], ['43', '46'])).
% 5.14/5.36  thf('48', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.14/5.36      inference('simplify', [status(thm)], ['47'])).
% 5.14/5.36  thf('49', plain,
% 5.14/5.36      (((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 5.14/5.36         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.36      inference('clc', [status(thm)], ['40', '48'])).
% 5.14/5.36  thf('50', plain,
% 5.14/5.36      (![X3 : $i, X5 : $i]:
% 5.14/5.36         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 5.14/5.36      inference('cnf', [status(esa)], [d3_tarski])).
% 5.14/5.36  thf(d4_xboole_0, axiom,
% 5.14/5.36    (![A:$i,B:$i,C:$i]:
% 5.14/5.36     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 5.14/5.36       ( ![D:$i]:
% 5.14/5.36         ( ( r2_hidden @ D @ C ) <=>
% 5.14/5.36           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 5.14/5.36  thf('51', plain,
% 5.14/5.36      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 5.14/5.36         (~ (r2_hidden @ X10 @ X9)
% 5.14/5.36          | (r2_hidden @ X10 @ X8)
% 5.14/5.36          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 5.14/5.36      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.14/5.36  thf('52', plain,
% 5.14/5.36      (![X7 : $i, X8 : $i, X10 : $i]:
% 5.14/5.36         ((r2_hidden @ X10 @ X8)
% 5.14/5.36          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 5.14/5.36      inference('simplify', [status(thm)], ['51'])).
% 5.14/5.36  thf('53', plain,
% 5.14/5.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.36         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 5.14/5.36          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 5.14/5.36      inference('sup-', [status(thm)], ['50', '52'])).
% 5.14/5.36  thf('54', plain,
% 5.14/5.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.14/5.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.14/5.36  thf('55', plain,
% 5.14/5.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.36         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 5.14/5.36          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 5.14/5.36      inference('sup-', [status(thm)], ['50', '52'])).
% 5.14/5.36  thf('56', plain,
% 5.14/5.36      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 5.14/5.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.36      inference('split', [status(esa)], ['2'])).
% 5.14/5.36  thf('57', plain,
% 5.14/5.36      (![X13 : $i, X14 : $i, X16 : $i]:
% 5.14/5.36         (~ (r2_hidden @ X16 @ X14)
% 5.14/5.36          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 5.14/5.36      inference('simplify', [status(thm)], ['19'])).
% 5.14/5.36  thf('58', plain,
% 5.14/5.36      ((![X0 : $i]:
% 5.14/5.36          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B)))
% 5.14/5.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.36      inference('sup-', [status(thm)], ['56', '57'])).
% 5.14/5.36  thf('59', plain,
% 5.14/5.36      ((![X0 : $i, X1 : $i]:
% 5.14/5.36          ((r1_tarski @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)) @ X1)
% 5.14/5.36           | ~ (r2_hidden @ 
% 5.14/5.36                (sk_C @ X1 @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A))) @ sk_B)))
% 5.14/5.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.36      inference('sup-', [status(thm)], ['55', '58'])).
% 5.14/5.36  thf('60', plain,
% 5.14/5.36      ((![X0 : $i, X1 : $i]:
% 5.14/5.36          (~ (r2_hidden @ 
% 5.14/5.36              (sk_C @ X1 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0)) @ sk_B)
% 5.14/5.36           | (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)) @ X1)))
% 5.14/5.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.36      inference('sup-', [status(thm)], ['54', '59'])).
% 5.14/5.36  thf('61', plain,
% 5.14/5.36      ((![X0 : $i]:
% 5.14/5.36          ((r1_tarski @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)
% 5.14/5.36           | (r1_tarski @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)))
% 5.14/5.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.36      inference('sup-', [status(thm)], ['53', '60'])).
% 5.14/5.36  thf('62', plain,
% 5.14/5.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.14/5.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.14/5.36  thf('63', plain,
% 5.14/5.36      ((![X0 : $i]:
% 5.14/5.36          ((r1_tarski @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 5.14/5.36           | (r1_tarski @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)))
% 5.14/5.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.36      inference('demod', [status(thm)], ['61', '62'])).
% 5.14/5.36  thf('64', plain,
% 5.14/5.36      ((![X0 : $i]:
% 5.14/5.36          (r1_tarski @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))
% 5.14/5.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.36      inference('simplify', [status(thm)], ['63'])).
% 5.14/5.36  thf('65', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.14/5.36      inference('sup-', [status(thm)], ['23', '26'])).
% 5.14/5.36  thf('66', plain,
% 5.14/5.36      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.14/5.36      inference('sup-', [status(thm)], ['24', '25'])).
% 5.14/5.36  thf('67', plain,
% 5.14/5.36      (![X0 : $i, X1 : $i]:
% 5.14/5.36         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 5.14/5.36      inference('sup-', [status(thm)], ['65', '66'])).
% 5.14/5.36  thf('68', plain,
% 5.14/5.36      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 5.14/5.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.36      inference('sup-', [status(thm)], ['64', '67'])).
% 5.14/5.36  thf('69', plain,
% 5.14/5.36      (![X21 : $i, X22 : $i]:
% 5.14/5.36         ((k4_xboole_0 @ X21 @ X22)
% 5.14/5.36           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 5.14/5.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.14/5.36  thf('70', plain,
% 5.14/5.36      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 5.14/5.36          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 5.14/5.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.36      inference('sup+', [status(thm)], ['68', '69'])).
% 5.14/5.36  thf('71', plain,
% 5.14/5.36      (![X13 : $i, X14 : $i, X16 : $i]:
% 5.14/5.36         (~ (r2_hidden @ X16 @ X14)
% 5.14/5.36          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 5.14/5.36      inference('simplify', [status(thm)], ['19'])).
% 5.14/5.36  thf('72', plain,
% 5.14/5.36      ((![X0 : $i]:
% 5.14/5.36          (~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 5.14/5.36           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))))
% 5.14/5.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.36      inference('sup-', [status(thm)], ['70', '71'])).
% 5.14/5.36  thf('73', plain,
% 5.14/5.36      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 5.14/5.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.36             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.36      inference('sup-', [status(thm)], ['49', '72'])).
% 5.14/5.36  thf('74', plain,
% 5.14/5.36      ((((k1_xboole_0) = (k1_tarski @ sk_A)))
% 5.14/5.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.36             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.36      inference('sup-', [status(thm)], ['28', '73'])).
% 5.14/5.36  thf('75', plain,
% 5.14/5.36      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.36      inference('split', [status(esa)], ['0'])).
% 5.14/5.36  thf(d1_enumset1, axiom,
% 5.14/5.36    (![A:$i,B:$i,C:$i,D:$i]:
% 5.14/5.36     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 5.14/5.36       ( ![E:$i]:
% 5.14/5.36         ( ( r2_hidden @ E @ D ) <=>
% 5.14/5.36           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 5.14/5.36  thf(zf_stmt_1, axiom,
% 5.14/5.36    (![E:$i,C:$i,B:$i,A:$i]:
% 5.14/5.36     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 5.14/5.37       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 5.14/5.37  thf('76', plain,
% 5.14/5.37      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 5.14/5.37         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 5.14/5.37          | ((X29) = (X30))
% 5.14/5.37          | ((X29) = (X31))
% 5.14/5.37          | ((X29) = (X32)))),
% 5.14/5.37      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.14/5.37  thf('77', plain,
% 5.14/5.37      (![X3 : $i, X5 : $i]:
% 5.14/5.37         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 5.14/5.37      inference('cnf', [status(esa)], [d3_tarski])).
% 5.14/5.37  thf('78', plain,
% 5.14/5.37      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 5.14/5.37      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.14/5.37  thf(t70_enumset1, axiom,
% 5.14/5.37    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 5.14/5.37  thf('79', plain,
% 5.14/5.37      (![X41 : $i, X42 : $i]:
% 5.14/5.37         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 5.14/5.37      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.14/5.37  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 5.14/5.37  thf(zf_stmt_3, axiom,
% 5.14/5.37    (![A:$i,B:$i,C:$i,D:$i]:
% 5.14/5.37     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 5.14/5.37       ( ![E:$i]:
% 5.14/5.37         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 5.14/5.37  thf('80', plain,
% 5.14/5.37      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X38 @ X37)
% 5.14/5.37          | ~ (zip_tseitin_0 @ X38 @ X34 @ X35 @ X36)
% 5.14/5.37          | ((X37) != (k1_enumset1 @ X36 @ X35 @ X34)))),
% 5.14/5.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.14/5.37  thf('81', plain,
% 5.14/5.37      (![X34 : $i, X35 : $i, X36 : $i, X38 : $i]:
% 5.14/5.37         (~ (zip_tseitin_0 @ X38 @ X34 @ X35 @ X36)
% 5.14/5.37          | ~ (r2_hidden @ X38 @ (k1_enumset1 @ X36 @ X35 @ X34)))),
% 5.14/5.37      inference('simplify', [status(thm)], ['80'])).
% 5.14/5.37  thf('82', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 5.14/5.37          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 5.14/5.37      inference('sup-', [status(thm)], ['79', '81'])).
% 5.14/5.37  thf('83', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 5.14/5.37          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['78', '82'])).
% 5.14/5.37  thf('84', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 5.14/5.37          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['77', '83'])).
% 5.14/5.37  thf('85', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 5.14/5.37          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 5.14/5.37          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 5.14/5.37          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 5.14/5.37      inference('sup-', [status(thm)], ['76', '84'])).
% 5.14/5.37  thf('86', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 5.14/5.37          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 5.14/5.37      inference('simplify', [status(thm)], ['85'])).
% 5.14/5.37  thf('87', plain,
% 5.14/5.37      (![X3 : $i, X5 : $i]:
% 5.14/5.37         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 5.14/5.37      inference('cnf', [status(esa)], [d3_tarski])).
% 5.14/5.37  thf('88', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X0 @ X1)
% 5.14/5.37          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 5.14/5.37          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 5.14/5.37      inference('sup-', [status(thm)], ['86', '87'])).
% 5.14/5.37  thf('89', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 5.14/5.37      inference('simplify', [status(thm)], ['88'])).
% 5.14/5.37  thf('90', plain,
% 5.14/5.37      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 5.14/5.37         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['75', '89'])).
% 5.14/5.37  thf('91', plain,
% 5.14/5.37      (![X23 : $i, X24 : $i]:
% 5.14/5.37         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 5.14/5.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.14/5.37  thf('92', plain,
% 5.14/5.37      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 5.14/5.37         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['90', '91'])).
% 5.14/5.37  thf('93', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.14/5.37  thf('94', plain,
% 5.14/5.37      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 5.14/5.37         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('demod', [status(thm)], ['92', '93'])).
% 5.14/5.37  thf('95', plain,
% 5.14/5.37      (![X21 : $i, X22 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X21 @ X22)
% 5.14/5.37           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 5.14/5.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.14/5.37  thf('96', plain,
% 5.14/5.37      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 5.14/5.37          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 5.14/5.37         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['94', '95'])).
% 5.14/5.37  thf('97', plain,
% 5.14/5.37      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 5.14/5.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.14/5.37  thf('98', plain,
% 5.14/5.37      (((r1_tarski @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B))
% 5.14/5.37         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['96', '97'])).
% 5.14/5.37  thf('99', plain,
% 5.14/5.37      (![X18 : $i, X20 : $i]:
% 5.14/5.37         (((X18) = (X20))
% 5.14/5.37          | ~ (r1_tarski @ X20 @ X18)
% 5.14/5.37          | ~ (r1_tarski @ X18 @ X20))),
% 5.14/5.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.14/5.37  thf('100', plain,
% 5.14/5.37      (((~ (r1_tarski @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 5.14/5.37         | ((sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 5.14/5.37         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['98', '99'])).
% 5.14/5.37  thf('101', plain,
% 5.14/5.37      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 5.14/5.37          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 5.14/5.37         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['94', '95'])).
% 5.14/5.37  thf('102', plain,
% 5.14/5.37      (![X46 : $i, X47 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X46 @ X47)
% 5.14/5.37          | ((k4_xboole_0 @ X47 @ (k1_tarski @ X46)) != (X47)))),
% 5.14/5.37      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 5.14/5.37  thf('103', plain,
% 5.14/5.37      (((((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))
% 5.14/5.37         | ~ (r2_hidden @ sk_A @ sk_B))) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['101', '102'])).
% 5.14/5.37  thf('104', plain,
% 5.14/5.37      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('split', [status(esa)], ['0'])).
% 5.14/5.37  thf('105', plain,
% 5.14/5.37      ((((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B)))
% 5.14/5.37         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('demod', [status(thm)], ['103', '104'])).
% 5.14/5.37  thf('106', plain,
% 5.14/5.37      ((~ (r1_tarski @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 5.14/5.37         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('simplify_reflect-', [status(thm)], ['100', '105'])).
% 5.14/5.37  thf('107', plain,
% 5.14/5.37      ((~ (r1_tarski @ sk_B @ (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['74', '106'])).
% 5.14/5.37  thf('108', plain,
% 5.14/5.37      (![X47 : $i, X48 : $i]:
% 5.14/5.37         (((k4_xboole_0 @ X47 @ (k1_tarski @ X48)) = (X47))
% 5.14/5.37          | (r2_hidden @ X48 @ X47))),
% 5.14/5.37      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 5.14/5.37  thf('109', plain,
% 5.14/5.37      ((((k1_xboole_0) = (k1_tarski @ sk_A)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['28', '73'])).
% 5.14/5.37  thf('110', plain,
% 5.14/5.37      (![X7 : $i, X8 : $i, X11 : $i]:
% 5.14/5.37         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 5.14/5.37          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 5.14/5.37          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 5.14/5.37      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.14/5.37  thf('111', plain,
% 5.14/5.37      (![X7 : $i, X8 : $i, X11 : $i]:
% 5.14/5.37         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 5.14/5.37          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 5.14/5.37          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 5.14/5.37      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.14/5.37  thf('112', plain,
% 5.14/5.37      ((![X0 : $i]:
% 5.14/5.37          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.37      inference('sup-', [status(thm)], ['56', '57'])).
% 5.14/5.37  thf('113', plain,
% 5.14/5.37      ((![X0 : $i, X1 : $i]:
% 5.14/5.37          ((r2_hidden @ (sk_D @ X1 @ (k1_tarski @ sk_A) @ X0) @ X1)
% 5.14/5.37           | ((X1) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 5.14/5.37           | ~ (r2_hidden @ (sk_D @ X1 @ (k1_tarski @ sk_A) @ X0) @ sk_B)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.37      inference('sup-', [status(thm)], ['111', '112'])).
% 5.14/5.37  thf('114', plain,
% 5.14/5.37      ((![X0 : $i]:
% 5.14/5.37          ((r2_hidden @ (sk_D @ X0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)
% 5.14/5.37           | ((X0) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 5.14/5.37           | ((X0) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 5.14/5.37           | (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.37      inference('sup-', [status(thm)], ['110', '113'])).
% 5.14/5.37  thf('115', plain,
% 5.14/5.37      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.37      inference('sup-', [status(thm)], ['64', '67'])).
% 5.14/5.37  thf('116', plain,
% 5.14/5.37      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.37      inference('sup-', [status(thm)], ['64', '67'])).
% 5.14/5.37  thf('117', plain,
% 5.14/5.37      ((![X0 : $i]:
% 5.14/5.37          ((r2_hidden @ (sk_D @ X0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)
% 5.14/5.37           | ((X0) = (k1_xboole_0))
% 5.14/5.37           | ((X0) = (k1_xboole_0))
% 5.14/5.37           | (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.37      inference('demod', [status(thm)], ['114', '115', '116'])).
% 5.14/5.37  thf('118', plain,
% 5.14/5.37      ((![X0 : $i]:
% 5.14/5.37          (((X0) = (k1_xboole_0))
% 5.14/5.37           | (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 5.14/5.37      inference('simplify', [status(thm)], ['117'])).
% 5.14/5.37  thf('119', plain,
% 5.14/5.37      ((![X0 : $i]:
% 5.14/5.37          ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ sk_B) @ X0)
% 5.14/5.37           | ((X0) = (k1_xboole_0))))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['109', '118'])).
% 5.14/5.37  thf('120', plain,
% 5.14/5.37      (![X47 : $i, X48 : $i]:
% 5.14/5.37         (((k4_xboole_0 @ X47 @ (k1_tarski @ X48)) = (X47))
% 5.14/5.37          | (r2_hidden @ X48 @ X47))),
% 5.14/5.37      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 5.14/5.37  thf('121', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.37         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 5.14/5.37          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['50', '52'])).
% 5.14/5.37  thf('122', plain,
% 5.14/5.37      (![X3 : $i, X5 : $i]:
% 5.14/5.37         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 5.14/5.37      inference('cnf', [status(esa)], [d3_tarski])).
% 5.14/5.37  thf('123', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 5.14/5.37          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['121', '122'])).
% 5.14/5.37  thf('124', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 5.14/5.37      inference('simplify', [status(thm)], ['123'])).
% 5.14/5.37  thf('125', plain,
% 5.14/5.37      (![X23 : $i, X24 : $i]:
% 5.14/5.37         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 5.14/5.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.14/5.37  thf('126', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 5.14/5.37           = (k3_xboole_0 @ X1 @ X0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['124', '125'])).
% 5.14/5.37  thf('127', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.14/5.37  thf('128', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 5.14/5.37           = (k3_xboole_0 @ X1 @ X0))),
% 5.14/5.37      inference('demod', [status(thm)], ['126', '127'])).
% 5.14/5.37  thf('129', plain,
% 5.14/5.37      (![X21 : $i, X22 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X21 @ X22)
% 5.14/5.37           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 5.14/5.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.14/5.37  thf('130', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 5.14/5.37           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['128', '129'])).
% 5.14/5.37  thf('131', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.14/5.37  thf('132', plain,
% 5.14/5.37      (![X21 : $i, X22 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X21 @ X22)
% 5.14/5.37           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 5.14/5.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.14/5.37  thf('133', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X0 @ X1)
% 5.14/5.37           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['131', '132'])).
% 5.14/5.37  thf('134', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 5.14/5.37           = (k4_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('demod', [status(thm)], ['130', '133'])).
% 5.14/5.37  thf('135', plain,
% 5.14/5.37      (![X13 : $i, X14 : $i, X16 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X16 @ X14)
% 5.14/5.37          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 5.14/5.37      inference('simplify', [status(thm)], ['19'])).
% 5.14/5.37  thf('136', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 5.14/5.37          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['134', '135'])).
% 5.14/5.37  thf('137', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X2 @ X0)
% 5.14/5.37          | (r2_hidden @ X1 @ X0)
% 5.14/5.37          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['120', '136'])).
% 5.14/5.37  thf('138', plain,
% 5.14/5.37      (![X7 : $i, X8 : $i, X10 : $i]:
% 5.14/5.37         ((r2_hidden @ X10 @ X8)
% 5.14/5.37          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 5.14/5.37      inference('simplify', [status(thm)], ['51'])).
% 5.14/5.37  thf('139', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 5.14/5.37          | (r2_hidden @ X1 @ X0))),
% 5.14/5.37      inference('clc', [status(thm)], ['137', '138'])).
% 5.14/5.37  thf('140', plain,
% 5.14/5.37      ((![X0 : $i, X1 : $i]:
% 5.14/5.37          (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0))
% 5.14/5.37           | (r2_hidden @ X1 @ X0)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['119', '139'])).
% 5.14/5.37  thf('141', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 5.14/5.37           = (k4_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('demod', [status(thm)], ['130', '133'])).
% 5.14/5.37  thf('142', plain,
% 5.14/5.37      ((![X0 : $i, X1 : $i]:
% 5.14/5.37          (((k4_xboole_0 @ X1 @ k1_xboole_0)
% 5.14/5.37             = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.14/5.37           | (r2_hidden @ X0 @ X1)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['140', '141'])).
% 5.14/5.37  thf('143', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.14/5.37      inference('sup+', [status(thm)], ['33', '34'])).
% 5.14/5.37  thf('144', plain,
% 5.14/5.37      ((![X0 : $i, X1 : $i]:
% 5.14/5.37          (((k5_xboole_0 @ X1 @ k1_xboole_0)
% 5.14/5.37             = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.14/5.37           | (r2_hidden @ X0 @ X1)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('demod', [status(thm)], ['142', '143'])).
% 5.14/5.37  thf('145', plain,
% 5.14/5.37      ((![X0 : $i, X1 : $i]:
% 5.14/5.37          (((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 5.14/5.37           | (r2_hidden @ X1 @ X0)
% 5.14/5.37           | (r2_hidden @ X1 @ X0)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['108', '144'])).
% 5.14/5.37  thf('146', plain,
% 5.14/5.37      ((![X0 : $i, X1 : $i]:
% 5.14/5.37          ((r2_hidden @ X1 @ X0) | ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('simplify', [status(thm)], ['145'])).
% 5.14/5.37  thf('147', plain,
% 5.14/5.37      (((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 5.14/5.37         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('clc', [status(thm)], ['40', '48'])).
% 5.14/5.37  thf('148', plain,
% 5.14/5.37      ((((k1_xboole_0) = (k1_tarski @ sk_A)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['28', '73'])).
% 5.14/5.37  thf('149', plain,
% 5.14/5.37      (![X46 : $i, X47 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X46 @ X47)
% 5.14/5.37          | ((k4_xboole_0 @ X47 @ (k1_tarski @ X46)) != (X47)))),
% 5.14/5.37      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 5.14/5.37  thf('150', plain,
% 5.14/5.37      ((![X0 : $i]:
% 5.14/5.37          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 5.14/5.37           | ~ (r2_hidden @ sk_A @ X0)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['148', '149'])).
% 5.14/5.37  thf('151', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.14/5.37      inference('sup+', [status(thm)], ['33', '34'])).
% 5.14/5.37  thf('152', plain,
% 5.14/5.37      ((![X0 : $i]:
% 5.14/5.37          (((k5_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 5.14/5.37           | ~ (r2_hidden @ sk_A @ X0)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('demod', [status(thm)], ['150', '151'])).
% 5.14/5.37  thf('153', plain,
% 5.14/5.37      ((((k5_xboole_0 @ (k5_xboole_0 @ sk_B @ k1_xboole_0) @ k1_xboole_0)
% 5.14/5.37          != (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['147', '152'])).
% 5.14/5.37  thf('154', plain,
% 5.14/5.37      ((![X0 : $i]:
% 5.14/5.37          (((k5_xboole_0 @ sk_B @ k1_xboole_0)
% 5.14/5.37             != (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 5.14/5.37           | (r2_hidden @ X0 @ (k5_xboole_0 @ sk_B @ k1_xboole_0))))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['146', '153'])).
% 5.14/5.37  thf('155', plain,
% 5.14/5.37      ((![X0 : $i]: (r2_hidden @ X0 @ (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('simplify', [status(thm)], ['154'])).
% 5.14/5.37  thf('156', plain,
% 5.14/5.37      (![X3 : $i, X5 : $i]:
% 5.14/5.37         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 5.14/5.37      inference('cnf', [status(esa)], [d3_tarski])).
% 5.14/5.37  thf('157', plain,
% 5.14/5.37      ((![X0 : $i]: (r1_tarski @ X0 @ (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 5.14/5.37         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 5.14/5.37             ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['155', '156'])).
% 5.14/5.37  thf('158', plain,
% 5.14/5.37      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 5.14/5.37       ~ ((r2_hidden @ sk_A @ sk_B))),
% 5.14/5.37      inference('demod', [status(thm)], ['107', '157'])).
% 5.14/5.37  thf('159', plain,
% 5.14/5.37      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 5.14/5.37       ((r2_hidden @ sk_A @ sk_B))),
% 5.14/5.37      inference('split', [status(esa)], ['0'])).
% 5.14/5.37  thf('160', plain,
% 5.14/5.37      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 5.14/5.37      inference('sat_resolution*', [status(thm)], ['3', '158', '159'])).
% 5.14/5.37  thf('161', plain,
% 5.14/5.37      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 5.14/5.37      inference('simpl_trail', [status(thm)], ['1', '160'])).
% 5.14/5.37  thf('162', plain,
% 5.14/5.37      (![X47 : $i, X48 : $i]:
% 5.14/5.37         (((k4_xboole_0 @ X47 @ (k1_tarski @ X48)) = (X47))
% 5.14/5.37          | (r2_hidden @ X48 @ X47))),
% 5.14/5.37      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 5.14/5.37  thf('163', plain,
% 5.14/5.37      (![X7 : $i, X8 : $i, X11 : $i]:
% 5.14/5.37         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 5.14/5.37          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 5.14/5.37          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 5.14/5.37      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.14/5.37  thf('164', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.14/5.37      inference('simplify', [status(thm)], ['47'])).
% 5.14/5.37  thf('165', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 5.14/5.37          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['163', '164'])).
% 5.14/5.37  thf('166', plain,
% 5.14/5.37      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 5.14/5.37      inference('sup+', [status(thm)], ['31', '32'])).
% 5.14/5.37  thf('167', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 5.14/5.37          | ((X1) = (k1_xboole_0)))),
% 5.14/5.37      inference('demod', [status(thm)], ['165', '166'])).
% 5.14/5.37  thf('168', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.14/5.37  thf('169', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 5.14/5.37          | (r2_hidden @ X1 @ X0))),
% 5.14/5.37      inference('clc', [status(thm)], ['137', '138'])).
% 5.14/5.37  thf('170', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.14/5.37          | (r2_hidden @ X0 @ X1))),
% 5.14/5.37      inference('sup-', [status(thm)], ['168', '169'])).
% 5.14/5.37  thf('171', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 5.14/5.37          | (r2_hidden @ X0 @ X1))),
% 5.14/5.37      inference('sup-', [status(thm)], ['167', '170'])).
% 5.14/5.37  thf('172', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.14/5.37  thf('173', plain,
% 5.14/5.37      (![X7 : $i, X8 : $i, X11 : $i]:
% 5.14/5.37         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 5.14/5.37          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 5.14/5.37          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 5.14/5.37      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.14/5.37  thf('174', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 5.14/5.37      inference('clc', [status(thm)], ['17', '21'])).
% 5.14/5.37  thf('175', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.37         ((r2_hidden @ (sk_D @ X2 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ X2)
% 5.14/5.37          | ((X2) = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['173', '174'])).
% 5.14/5.37  thf('176', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['23', '26'])).
% 5.14/5.37  thf('177', plain,
% 5.14/5.37      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['29', '30'])).
% 5.14/5.37  thf('178', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 5.14/5.37      inference('sup+', [status(thm)], ['176', '177'])).
% 5.14/5.37  thf('179', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.37         ((r2_hidden @ (sk_D @ X2 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ X2)
% 5.14/5.37          | ((X2) = (k1_xboole_0)))),
% 5.14/5.37      inference('demod', [status(thm)], ['175', '178'])).
% 5.14/5.37  thf('180', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 5.14/5.37           = (k4_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('demod', [status(thm)], ['130', '133'])).
% 5.14/5.37  thf('181', plain,
% 5.14/5.37      (![X47 : $i, X48 : $i]:
% 5.14/5.37         (((k4_xboole_0 @ X47 @ (k1_tarski @ X48)) = (X47))
% 5.14/5.37          | (r2_hidden @ X48 @ X47))),
% 5.14/5.37      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 5.14/5.37  thf('182', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 5.14/5.37          | ((X1) = (k1_xboole_0)))),
% 5.14/5.37      inference('demod', [status(thm)], ['165', '166'])).
% 5.14/5.37  thf('183', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 5.14/5.37          | (r2_hidden @ X1 @ X0))),
% 5.14/5.37      inference('clc', [status(thm)], ['137', '138'])).
% 5.14/5.37  thf('184', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0))
% 5.14/5.37          | (r2_hidden @ X1 @ X0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['182', '183'])).
% 5.14/5.37  thf('185', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X0 @ X1)
% 5.14/5.37           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['131', '132'])).
% 5.14/5.37  thf('186', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 5.14/5.37            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 5.14/5.37          | (r2_hidden @ X1 @ X0))),
% 5.14/5.37      inference('sup+', [status(thm)], ['184', '185'])).
% 5.14/5.37  thf('187', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 5.14/5.37          | (r2_hidden @ X1 @ X0)
% 5.14/5.37          | (r2_hidden @ X1 @ X0))),
% 5.14/5.37      inference('sup+', [status(thm)], ['181', '186'])).
% 5.14/5.37  thf('188', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((r2_hidden @ X1 @ X0) | ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 5.14/5.37      inference('simplify', [status(thm)], ['187'])).
% 5.14/5.37  thf('189', plain,
% 5.14/5.37      (![X7 : $i, X8 : $i, X11 : $i]:
% 5.14/5.37         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 5.14/5.37          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 5.14/5.37          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 5.14/5.37      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.14/5.37  thf('190', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.14/5.37      inference('simplify', [status(thm)], ['47'])).
% 5.14/5.37  thf('191', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 5.14/5.37          | ((X1) = (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['189', '190'])).
% 5.14/5.37  thf('192', plain,
% 5.14/5.37      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['29', '30'])).
% 5.14/5.37  thf('193', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 5.14/5.37          | ((X1) = (k1_xboole_0)))),
% 5.14/5.37      inference('demod', [status(thm)], ['191', '192'])).
% 5.14/5.37  thf('194', plain,
% 5.14/5.37      (![X13 : $i, X14 : $i, X16 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X16 @ X14)
% 5.14/5.37          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 5.14/5.37      inference('simplify', [status(thm)], ['19'])).
% 5.14/5.37  thf('195', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.37         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 5.14/5.37          | ~ (r2_hidden @ 
% 5.14/5.37               (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ X0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['193', '194'])).
% 5.14/5.37  thf('196', plain,
% 5.14/5.37      (![X0 : $i, X2 : $i]:
% 5.14/5.37         (((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 5.14/5.37          | ((k4_xboole_0 @ X2 @ X0) = (k1_xboole_0)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['188', '195'])).
% 5.14/5.37  thf('197', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((r2_hidden @ X1 @ X0) | ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 5.14/5.37      inference('simplify', [status(thm)], ['187'])).
% 5.14/5.37  thf('198', plain,
% 5.14/5.37      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 5.14/5.37      inference('split', [status(esa)], ['2'])).
% 5.14/5.37  thf('199', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 5.14/5.37      inference('sat_resolution*', [status(thm)], ['3', '158'])).
% 5.14/5.37  thf('200', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 5.14/5.37      inference('simpl_trail', [status(thm)], ['198', '199'])).
% 5.14/5.37  thf('201', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['197', '200'])).
% 5.14/5.37  thf('202', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (((sk_B) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ X1 @ X0)))
% 5.14/5.37          | ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['196', '201'])).
% 5.14/5.37  thf('203', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (((sk_B) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ X1 @ X0)))
% 5.14/5.37          | ((k3_xboole_0 @ X0 @ X1)
% 5.14/5.37              = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ k1_xboole_0)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['180', '202'])).
% 5.14/5.37  thf('204', plain,
% 5.14/5.37      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 5.14/5.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.14/5.37  thf('205', plain,
% 5.14/5.37      (![X23 : $i, X24 : $i]:
% 5.14/5.37         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 5.14/5.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.14/5.37  thf('206', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 5.14/5.37           = (k4_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('sup-', [status(thm)], ['204', '205'])).
% 5.14/5.37  thf('207', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.14/5.37  thf('208', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 5.14/5.37           = (k4_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('demod', [status(thm)], ['206', '207'])).
% 5.14/5.37  thf('209', plain,
% 5.14/5.37      (![X21 : $i, X22 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X21 @ X22)
% 5.14/5.37           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 5.14/5.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.14/5.37  thf('210', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 5.14/5.37           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['208', '209'])).
% 5.14/5.37  thf('211', plain,
% 5.14/5.37      (![X13 : $i, X14 : $i, X16 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X16 @ X14)
% 5.14/5.37          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 5.14/5.37      inference('simplify', [status(thm)], ['19'])).
% 5.14/5.37  thf('212', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 5.14/5.37          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['210', '211'])).
% 5.14/5.37  thf('213', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X1 @ sk_B)
% 5.14/5.37          | ((k3_xboole_0 @ X0 @ sk_B)
% 5.14/5.37              = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ k1_xboole_0))
% 5.14/5.37          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ sk_B @ X0)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['203', '212'])).
% 5.14/5.37  thf('214', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.37         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['14', '15'])).
% 5.14/5.37  thf('215', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ sk_B @ X0))
% 5.14/5.37          | ((k3_xboole_0 @ X0 @ sk_B)
% 5.14/5.37              = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ k1_xboole_0)))),
% 5.14/5.37      inference('clc', [status(thm)], ['213', '214'])).
% 5.14/5.37  thf('216', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         (((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 5.14/5.37          | ((k3_xboole_0 @ X0 @ sk_B)
% 5.14/5.37              = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ k1_xboole_0)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['179', '215'])).
% 5.14/5.37  thf('217', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         (((k3_xboole_0 @ X0 @ sk_B)
% 5.14/5.37            = (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ k1_xboole_0))
% 5.14/5.37          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['172', '216'])).
% 5.14/5.37  thf('218', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.14/5.37      inference('sup+', [status(thm)], ['33', '34'])).
% 5.14/5.37  thf('219', plain,
% 5.14/5.37      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 5.14/5.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.14/5.37  thf('220', plain,
% 5.14/5.37      (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 5.14/5.37      inference('sup+', [status(thm)], ['218', '219'])).
% 5.14/5.37  thf('221', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         ((r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ (k3_xboole_0 @ sk_B @ X0))
% 5.14/5.37          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['217', '220'])).
% 5.14/5.37  thf('222', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         ((r1_tarski @ (k3_xboole_0 @ (k1_tarski @ X0) @ sk_B) @ k1_xboole_0)
% 5.14/5.37          | (r2_hidden @ X0 @ sk_B)
% 5.14/5.37          | ((k4_xboole_0 @ sk_B @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['171', '221'])).
% 5.14/5.37  thf('223', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['23', '26'])).
% 5.14/5.37  thf('224', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 5.14/5.37      inference('sup-', [status(thm)], ['12', '22'])).
% 5.14/5.37  thf('225', plain,
% 5.14/5.37      (![X18 : $i, X20 : $i]:
% 5.14/5.37         (((X18) = (X20))
% 5.14/5.37          | ~ (r1_tarski @ X20 @ X18)
% 5.14/5.37          | ~ (r1_tarski @ X18 @ X20))),
% 5.14/5.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.14/5.37  thf('226', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ X1 @ X1))
% 5.14/5.37          | ((X0) = (k5_xboole_0 @ X1 @ X1)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['224', '225'])).
% 5.14/5.37  thf('227', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (~ (r1_tarski @ X1 @ k1_xboole_0) | ((X1) = (k5_xboole_0 @ X0 @ X0)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['223', '226'])).
% 5.14/5.37  thf('228', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (((k4_xboole_0 @ sk_B @ (k1_tarski @ X0)) = (k1_xboole_0))
% 5.14/5.37          | (r2_hidden @ X0 @ sk_B)
% 5.14/5.37          | ((k3_xboole_0 @ (k1_tarski @ X0) @ sk_B) = (k5_xboole_0 @ X1 @ X1)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['222', '227'])).
% 5.14/5.37  thf('229', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (((sk_B) = (k1_xboole_0))
% 5.14/5.37          | (r2_hidden @ X0 @ sk_B)
% 5.14/5.37          | ((k3_xboole_0 @ (k1_tarski @ X0) @ sk_B) = (k5_xboole_0 @ X1 @ X1))
% 5.14/5.37          | (r2_hidden @ X0 @ sk_B))),
% 5.14/5.37      inference('sup+', [status(thm)], ['162', '228'])).
% 5.14/5.37  thf('230', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (((k3_xboole_0 @ (k1_tarski @ X0) @ sk_B) = (k5_xboole_0 @ X1 @ X1))
% 5.14/5.37          | (r2_hidden @ X0 @ sk_B)
% 5.14/5.37          | ((sk_B) = (k1_xboole_0)))),
% 5.14/5.37      inference('simplify', [status(thm)], ['229'])).
% 5.14/5.37  thf('231', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.14/5.37  thf('232', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 5.14/5.37      inference('simplify', [status(thm)], ['123'])).
% 5.14/5.37  thf('233', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 5.14/5.37      inference('sup+', [status(thm)], ['231', '232'])).
% 5.14/5.37  thf('234', plain,
% 5.14/5.37      (![X23 : $i, X24 : $i]:
% 5.14/5.37         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 5.14/5.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.14/5.37  thf('235', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 5.14/5.37           = (k3_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('sup-', [status(thm)], ['233', '234'])).
% 5.14/5.37  thf('236', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.14/5.37  thf('237', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 5.14/5.37           = (k3_xboole_0 @ X0 @ X1))),
% 5.14/5.37      inference('demod', [status(thm)], ['235', '236'])).
% 5.14/5.37  thf('238', plain,
% 5.14/5.37      (![X21 : $i, X22 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X21 @ X22)
% 5.14/5.37           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 5.14/5.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.14/5.37  thf('239', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 5.14/5.37           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.14/5.37      inference('sup+', [status(thm)], ['237', '238'])).
% 5.14/5.37  thf('240', plain,
% 5.14/5.37      (![X21 : $i, X22 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X21 @ X22)
% 5.14/5.37           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 5.14/5.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.14/5.37  thf('241', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 5.14/5.37           = (k4_xboole_0 @ X1 @ X0))),
% 5.14/5.37      inference('demod', [status(thm)], ['239', '240'])).
% 5.14/5.37  thf('242', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (((k4_xboole_0 @ (k1_tarski @ X1) @ (k5_xboole_0 @ X0 @ X0))
% 5.14/5.37            = (k4_xboole_0 @ (k1_tarski @ X1) @ sk_B))
% 5.14/5.37          | ((sk_B) = (k1_xboole_0))
% 5.14/5.37          | (r2_hidden @ X1 @ sk_B))),
% 5.14/5.37      inference('sup+', [status(thm)], ['230', '241'])).
% 5.14/5.37  thf('243', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.14/5.37      inference('sup-', [status(thm)], ['23', '26'])).
% 5.14/5.37  thf('244', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.14/5.37      inference('sup+', [status(thm)], ['33', '34'])).
% 5.14/5.37  thf('245', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.14/5.37      inference('sup+', [status(thm)], ['33', '34'])).
% 5.14/5.37  thf('246', plain,
% 5.14/5.37      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 5.14/5.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.14/5.37  thf('247', plain,
% 5.14/5.37      (![X18 : $i, X20 : $i]:
% 5.14/5.37         (((X18) = (X20))
% 5.14/5.37          | ~ (r1_tarski @ X20 @ X18)
% 5.14/5.37          | ~ (r1_tarski @ X18 @ X20))),
% 5.14/5.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.14/5.37  thf('248', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 5.14/5.37          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['246', '247'])).
% 5.14/5.37  thf('249', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 5.14/5.37          | ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['245', '248'])).
% 5.14/5.37  thf('250', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.14/5.37      inference('sup+', [status(thm)], ['33', '34'])).
% 5.14/5.37  thf('251', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 5.14/5.37          | ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 5.14/5.37      inference('demod', [status(thm)], ['249', '250'])).
% 5.14/5.37  thf('252', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.14/5.37      inference('sup+', [status(thm)], ['33', '34'])).
% 5.14/5.37  thf('253', plain,
% 5.14/5.37      (![X3 : $i, X5 : $i]:
% 5.14/5.37         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 5.14/5.37      inference('cnf', [status(esa)], [d3_tarski])).
% 5.14/5.37  thf('254', plain,
% 5.14/5.37      (![X12 : $i, X13 : $i, X14 : $i]:
% 5.14/5.37         ((r2_hidden @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 5.14/5.37          | (r2_hidden @ X12 @ X14)
% 5.14/5.37          | ~ (r2_hidden @ X12 @ X13))),
% 5.14/5.37      inference('simplify', [status(thm)], ['37'])).
% 5.14/5.37  thf('255', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.14/5.37         ((r1_tarski @ X0 @ X1)
% 5.14/5.37          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 5.14/5.37          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['253', '254'])).
% 5.14/5.37  thf('256', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 5.14/5.37          | (r2_hidden @ (sk_C @ X1 @ X0) @ k1_xboole_0)
% 5.14/5.37          | (r1_tarski @ X0 @ X1))),
% 5.14/5.37      inference('sup+', [status(thm)], ['252', '255'])).
% 5.14/5.37  thf('257', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.14/5.37      inference('simplify', [status(thm)], ['47'])).
% 5.14/5.37  thf('258', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((r1_tarski @ X0 @ X1)
% 5.14/5.37          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 5.14/5.37      inference('clc', [status(thm)], ['256', '257'])).
% 5.14/5.37  thf('259', plain,
% 5.14/5.37      (![X3 : $i, X5 : $i]:
% 5.14/5.37         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 5.14/5.37      inference('cnf', [status(esa)], [d3_tarski])).
% 5.14/5.37  thf('260', plain,
% 5.14/5.37      (![X0 : $i]:
% 5.14/5.37         ((r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 5.14/5.37          | (r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['258', '259'])).
% 5.14/5.37  thf('261', plain,
% 5.14/5.37      (![X0 : $i]: (r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.14/5.37      inference('simplify', [status(thm)], ['260'])).
% 5.14/5.37  thf('262', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.14/5.37      inference('demod', [status(thm)], ['251', '261'])).
% 5.14/5.37  thf('263', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.14/5.37      inference('demod', [status(thm)], ['244', '262'])).
% 5.14/5.37  thf('264', plain,
% 5.14/5.37      (![X0 : $i, X1 : $i]:
% 5.14/5.37         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 5.14/5.37      inference('sup+', [status(thm)], ['243', '263'])).
% 5.14/5.37  thf('265', plain,
% 5.14/5.37      (![X1 : $i]:
% 5.14/5.37         (((k1_tarski @ X1) = (k4_xboole_0 @ (k1_tarski @ X1) @ sk_B))
% 5.14/5.37          | ((sk_B) = (k1_xboole_0))
% 5.14/5.37          | (r2_hidden @ X1 @ sk_B))),
% 5.14/5.37      inference('demod', [status(thm)], ['242', '264'])).
% 5.14/5.37  thf('266', plain,
% 5.14/5.37      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 5.14/5.37      inference('simpl_trail', [status(thm)], ['1', '160'])).
% 5.14/5.37  thf('267', plain,
% 5.14/5.37      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 5.14/5.37        | (r2_hidden @ sk_A @ sk_B)
% 5.14/5.37        | ((sk_B) = (k1_xboole_0)))),
% 5.14/5.37      inference('sup-', [status(thm)], ['265', '266'])).
% 5.14/5.37  thf('268', plain, ((((sk_B) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B))),
% 5.14/5.37      inference('simplify', [status(thm)], ['267'])).
% 5.14/5.37  thf('269', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 5.14/5.37      inference('simpl_trail', [status(thm)], ['198', '199'])).
% 5.14/5.37  thf('270', plain, (((sk_B) = (k1_xboole_0))),
% 5.14/5.37      inference('clc', [status(thm)], ['268', '269'])).
% 5.14/5.37  thf('271', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.14/5.37      inference('demod', [status(thm)], ['244', '262'])).
% 5.14/5.37  thf('272', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 5.14/5.37      inference('demod', [status(thm)], ['161', '270', '271'])).
% 5.14/5.37  thf('273', plain, ($false), inference('simplify', [status(thm)], ['272'])).
% 5.14/5.37  
% 5.14/5.37  % SZS output end Refutation
% 5.14/5.37  
% 5.21/5.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
