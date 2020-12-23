%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.izN4GOHEZF

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:03 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 201 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :   17
%              Number of atoms          :  646 (1382 expanded)
%              Number of equality atoms :   63 ( 154 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('15',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X9 ) )
      | ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X39: $i,X41: $i,X42: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X39 @ X41 ) @ X42 )
      | ~ ( r2_hidden @ X41 @ X42 )
      | ~ ( r2_hidden @ X39 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ sk_B ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ sk_A ) @ ( k5_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ ( k5_xboole_0 @ X0 @ sk_B ) )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ sk_B ) )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ sk_B ) )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ sk_B ) )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ sk_B ) )
        = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ sk_B ) )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['28','34','45'])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('60',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','60'])).

thf('62',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('63',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('65',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('68',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.izN4GOHEZF
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 405 iterations in 0.166s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.62  thf(commutativity_k2_tarski, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      (![X25 : $i, X26 : $i]:
% 0.38/0.62         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.62  thf(l51_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (![X37 : $i, X38 : $i]:
% 0.38/0.62         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 0.38/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['0', '1'])).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X37 : $i, X38 : $i]:
% 0.38/0.62         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 0.38/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.62  thf('4', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.62  thf(t1_boole, axiom,
% 0.38/0.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.62  thf('5', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.38/0.62  thf('6', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.38/0.62  thf(t39_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.62  thf('7', plain,
% 0.38/0.62      (![X19 : $i, X20 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 0.38/0.62           = (k2_xboole_0 @ X19 @ X20))),
% 0.38/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.62  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.38/0.62  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf(t98_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (![X23 : $i, X24 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X23 @ X24)
% 0.38/0.62           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['10', '11'])).
% 0.38/0.62  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.38/0.62  thf('14', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.62  thf(t46_zfmisc_1, conjecture,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r2_hidden @ A @ B ) =>
% 0.38/0.62       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i,B:$i]:
% 0.38/0.62        ( ( r2_hidden @ A @ B ) =>
% 0.38/0.62          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.38/0.62  thf('15', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t1_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.38/0.62       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.38/0.62         ((r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X9))
% 0.38/0.62          | (r2_hidden @ X6 @ X7)
% 0.38/0.62          | ~ (r2_hidden @ X6 @ X9))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r2_hidden @ sk_A @ X0)
% 0.38/0.62          | (r2_hidden @ sk_A @ (k5_xboole_0 @ X0 @ sk_B)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.62  thf('18', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r2_hidden @ sk_A @ X0)
% 0.38/0.62          | (r2_hidden @ sk_A @ (k5_xboole_0 @ X0 @ sk_B)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.62  thf(t38_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.38/0.62       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      (![X39 : $i, X41 : $i, X42 : $i]:
% 0.38/0.62         ((r1_tarski @ (k2_tarski @ X39 @ X41) @ X42)
% 0.38/0.62          | ~ (r2_hidden @ X41 @ X42)
% 0.38/0.62          | ~ (r2_hidden @ X39 @ X42))),
% 0.38/0.62      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((r2_hidden @ sk_A @ X0)
% 0.38/0.62          | ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ sk_B))
% 0.38/0.62          | (r1_tarski @ (k2_tarski @ X1 @ sk_A) @ (k5_xboole_0 @ X0 @ sk_B)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r2_hidden @ sk_A @ X0)
% 0.38/0.62          | (r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ (k5_xboole_0 @ X0 @ sk_B))
% 0.38/0.62          | (r2_hidden @ sk_A @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['17', '20'])).
% 0.38/0.62  thf(t69_enumset1, axiom,
% 0.38/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.38/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r2_hidden @ sk_A @ X0)
% 0.38/0.62          | (r1_tarski @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ X0 @ sk_B))
% 0.38/0.62          | (r2_hidden @ sk_A @ X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.62  thf('24', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ X0 @ sk_B))
% 0.38/0.62          | (r2_hidden @ sk_A @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.62  thf(t28_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.38/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r2_hidden @ sk_A @ X0)
% 0.38/0.62          | ((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ X0 @ sk_B))
% 0.38/0.62              = (k1_tarski @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.62  thf(t100_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      (![X13 : $i, X14 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X13 @ X14)
% 0.38/0.62           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.62  thf('28', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ X0 @ sk_B))
% 0.38/0.62            = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.38/0.62          | (r2_hidden @ sk_A @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['26', '27'])).
% 0.38/0.62  thf(d10_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.38/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.62  thf('30', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.38/0.62      inference('simplify', [status(thm)], ['29'])).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.38/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.62  thf('32', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.62  thf('33', plain,
% 0.38/0.62      (![X13 : $i, X14 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X13 @ X14)
% 0.38/0.62           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['32', '33'])).
% 0.38/0.62  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.38/0.62  thf(t40_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.38/0.62  thf('36', plain,
% 0.38/0.62      (![X21 : $i, X22 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X22)
% 0.38/0.62           = (k4_xboole_0 @ X21 @ X22))),
% 0.38/0.62      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.38/0.62  thf('37', plain,
% 0.38/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['35', '36'])).
% 0.38/0.62  thf('38', plain,
% 0.38/0.62      (![X13 : $i, X14 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X13 @ X14)
% 0.38/0.62           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.62  thf('39', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.62  thf('40', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['38', '39'])).
% 0.38/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.62  thf('41', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 0.38/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.62  thf('42', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.38/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.62  thf('43', plain,
% 0.38/0.62      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.62  thf('44', plain,
% 0.38/0.62      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['40', '43'])).
% 0.38/0.62  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['37', '44'])).
% 0.38/0.62  thf('46', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ X0 @ sk_B))
% 0.38/0.62            = (k1_xboole_0))
% 0.38/0.62          | (r2_hidden @ sk_A @ X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['28', '34', '45'])).
% 0.38/0.62  thf('47', plain,
% 0.38/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))
% 0.38/0.62        | (r2_hidden @ sk_A @ k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['14', '46'])).
% 0.38/0.62  thf('48', plain,
% 0.38/0.62      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.62  thf('49', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.62  thf('50', plain,
% 0.38/0.62      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['48', '49'])).
% 0.38/0.62  thf('51', plain,
% 0.38/0.62      (![X13 : $i, X14 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X13 @ X14)
% 0.38/0.62           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.62  thf('52', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['50', '51'])).
% 0.38/0.62  thf('53', plain,
% 0.38/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X6 @ X7)
% 0.38/0.62          | ~ (r2_hidden @ X6 @ X8)
% 0.38/0.62          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.38/0.62  thf('54', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 0.38/0.62          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.38/0.62          | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.62  thf('55', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 0.38/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.62  thf(d3_tarski, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.62  thf('56', plain,
% 0.38/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X2 @ X3)
% 0.38/0.62          | (r2_hidden @ X2 @ X4)
% 0.38/0.62          | ~ (r1_tarski @ X3 @ X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.62  thf('57', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.38/0.62  thf('58', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.38/0.62      inference('clc', [status(thm)], ['54', '57'])).
% 0.38/0.62  thf('59', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.38/0.62  thf('60', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.38/0.62      inference('clc', [status(thm)], ['58', '59'])).
% 0.38/0.62  thf('61', plain,
% 0.38/0.62      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.38/0.62      inference('clc', [status(thm)], ['47', '60'])).
% 0.38/0.62  thf('62', plain,
% 0.38/0.62      (![X19 : $i, X20 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 0.38/0.62           = (k2_xboole_0 @ X19 @ X20))),
% 0.38/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.62  thf('63', plain,
% 0.38/0.62      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.38/0.62         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['61', '62'])).
% 0.38/0.62  thf('64', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.38/0.62  thf('65', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['63', '64'])).
% 0.38/0.62  thf('66', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('67', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.62  thf('68', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['66', '67'])).
% 0.38/0.62  thf('69', plain, ($false),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['65', '68'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
