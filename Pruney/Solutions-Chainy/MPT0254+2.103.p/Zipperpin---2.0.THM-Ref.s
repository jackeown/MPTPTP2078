%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5LAKkGKLGH

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:49 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  135 (1017 expanded)
%              Number of leaves         :   24 ( 351 expanded)
%              Depth                    :   26
%              Number of atoms          : 1223 (9015 expanded)
%              Number of equality atoms :  115 ( 991 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('23',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['23','24','27','28','29','30'])).

thf('32',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('50',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('52',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('57',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['31','52','55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('59',plain,
    ( sk_B_1
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('62',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('68',plain,
    ( sk_B_1
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['59','60','61','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('70',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('72',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('78',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('79',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','81'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('83',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('84',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X52 != X51 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X52 ) @ ( k1_tarski @ X51 ) )
       != ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('85',plain,(
    ! [X51: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X51 ) @ ( k1_tarski @ X51 ) )
     != ( k1_tarski @ X51 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('87',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('89',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','81'])).

thf('90',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('95',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('96',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','96'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('98',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('100',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['97','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','105'])).

thf('107',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','81'])).

thf('108',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88','89','106','107'])).

thf('109',plain,(
    $false ),
    inference(simplify,[status(thm)],['108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5LAKkGKLGH
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:42:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.51/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.69  % Solved by: fo/fo7.sh
% 0.51/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.69  % done 365 iterations in 0.214s
% 0.51/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.69  % SZS output start Refutation
% 0.51/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.51/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.69  thf(sk_B_type, type, sk_B: $i > $i).
% 0.51/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.69  thf(t7_xboole_0, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.51/0.69          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.51/0.69  thf('0', plain,
% 0.51/0.69      (![X11 : $i]:
% 0.51/0.69         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.51/0.69      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.51/0.69  thf(t49_zfmisc_1, conjecture,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.51/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.69    (~( ![A:$i,B:$i]:
% 0.51/0.69        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.51/0.69    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.51/0.69  thf('1', plain,
% 0.51/0.69      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(commutativity_k5_xboole_0, axiom,
% 0.51/0.69    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.51/0.69  thf('2', plain,
% 0.51/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.69  thf(t94_xboole_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( k2_xboole_0 @ A @ B ) =
% 0.51/0.69       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.51/0.69  thf('3', plain,
% 0.51/0.69      (![X19 : $i, X20 : $i]:
% 0.51/0.69         ((k2_xboole_0 @ X19 @ X20)
% 0.51/0.69           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 0.51/0.69              (k3_xboole_0 @ X19 @ X20)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.51/0.69  thf('4', plain,
% 0.51/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.69  thf('5', plain,
% 0.51/0.69      (![X19 : $i, X20 : $i]:
% 0.51/0.69         ((k2_xboole_0 @ X19 @ X20)
% 0.51/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ 
% 0.51/0.69              (k5_xboole_0 @ X19 @ X20)))),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.69  thf('6', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k2_xboole_0 @ X0 @ X1)
% 0.51/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['2', '5'])).
% 0.51/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.51/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.51/0.69  thf('7', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.69  thf('8', plain,
% 0.51/0.69      (![X19 : $i, X20 : $i]:
% 0.51/0.69         ((k2_xboole_0 @ X19 @ X20)
% 0.51/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ 
% 0.51/0.69              (k5_xboole_0 @ X19 @ X20)))),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.69  thf('9', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k2_xboole_0 @ X0 @ X1)
% 0.51/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['7', '8'])).
% 0.51/0.69  thf('10', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['6', '9'])).
% 0.51/0.69  thf('11', plain,
% 0.51/0.69      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.51/0.69      inference('demod', [status(thm)], ['1', '10'])).
% 0.51/0.69  thf('12', plain,
% 0.51/0.69      (![X19 : $i, X20 : $i]:
% 0.51/0.69         ((k2_xboole_0 @ X19 @ X20)
% 0.51/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ 
% 0.51/0.69              (k5_xboole_0 @ X19 @ X20)))),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.69  thf('13', plain,
% 0.51/0.69      (![X19 : $i, X20 : $i]:
% 0.51/0.69         ((k2_xboole_0 @ X19 @ X20)
% 0.51/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ 
% 0.51/0.69              (k5_xboole_0 @ X19 @ X20)))),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.69  thf('14', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.51/0.69           = (k5_xboole_0 @ 
% 0.51/0.69              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.51/0.69              (k2_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['12', '13'])).
% 0.51/0.69  thf('15', plain,
% 0.51/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.69  thf('16', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.51/0.69           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.51/0.69              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.51/0.69      inference('demod', [status(thm)], ['14', '15'])).
% 0.51/0.69  thf('17', plain,
% 0.51/0.69      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69         (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.51/0.69         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.51/0.69            (k3_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69             (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))),
% 0.51/0.69      inference('sup+', [status(thm)], ['11', '16'])).
% 0.51/0.69  thf('18', plain,
% 0.51/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.69  thf(t5_boole, axiom,
% 0.51/0.69    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.51/0.69  thf('19', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.51/0.69      inference('cnf', [status(esa)], [t5_boole])).
% 0.51/0.69  thf('20', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('21', plain,
% 0.51/0.69      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69         (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.51/0.69         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69            (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))),
% 0.51/0.69      inference('demod', [status(thm)], ['17', '20'])).
% 0.51/0.69  thf('22', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k2_xboole_0 @ X0 @ X1)
% 0.51/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['7', '8'])).
% 0.51/0.69  thf('23', plain,
% 0.51/0.69      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69         (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.51/0.69         = (k5_xboole_0 @ 
% 0.51/0.69            (k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69             (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))) @ 
% 0.51/0.69            (k5_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69             (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))),
% 0.51/0.69      inference('sup+', [status(thm)], ['21', '22'])).
% 0.51/0.69  thf('24', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['6', '9'])).
% 0.51/0.69  thf('25', plain,
% 0.51/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.69  thf(t91_xboole_1, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.51/0.69       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.51/0.69  thf('26', plain,
% 0.51/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.51/0.69           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.51/0.69  thf('27', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.51/0.69           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['25', '26'])).
% 0.51/0.69  thf(t100_xboole_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.51/0.69  thf('28', plain,
% 0.51/0.69      (![X12 : $i, X13 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X12 @ X13)
% 0.51/0.69           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.69  thf('29', plain,
% 0.51/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.69  thf('30', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.51/0.69           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['25', '26'])).
% 0.51/0.69  thf('31', plain,
% 0.51/0.69      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69         (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.51/0.69         = (k5_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69            (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.51/0.69             (k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69              (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))))),
% 0.51/0.69      inference('demod', [status(thm)], ['23', '24', '27', '28', '29', '30'])).
% 0.51/0.69  thf('32', plain,
% 0.51/0.69      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69         (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.51/0.69         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69            (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))),
% 0.51/0.69      inference('demod', [status(thm)], ['17', '20'])).
% 0.51/0.69  thf('33', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.69  thf('34', plain,
% 0.51/0.69      (![X12 : $i, X13 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X12 @ X13)
% 0.51/0.69           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.69  thf('35', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.51/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['33', '34'])).
% 0.51/0.69  thf('36', plain,
% 0.51/0.69      (((k4_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69         (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.51/0.69         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69            (k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69             (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))),
% 0.51/0.69      inference('sup+', [status(thm)], ['32', '35'])).
% 0.51/0.69  thf('37', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.51/0.69           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['25', '26'])).
% 0.51/0.69  thf('38', plain,
% 0.51/0.69      (((k4_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69         (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.51/0.69         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.51/0.69            (k5_xboole_0 @ sk_B_1 @ 
% 0.51/0.69             (k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69              (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))))),
% 0.51/0.69      inference('demod', [status(thm)], ['36', '37'])).
% 0.51/0.69  thf('39', plain,
% 0.51/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.69  thf(t92_xboole_1, axiom,
% 0.51/0.69    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.51/0.69  thf('40', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.51/0.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.51/0.69  thf('41', plain,
% 0.51/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.51/0.69           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.51/0.69  thf('42', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.51/0.69           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['40', '41'])).
% 0.51/0.69  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('44', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('demod', [status(thm)], ['42', '43'])).
% 0.51/0.69  thf('45', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['39', '44'])).
% 0.51/0.69  thf('46', plain,
% 0.51/0.69      (((k1_tarski @ sk_A)
% 0.51/0.69         = (k5_xboole_0 @ 
% 0.51/0.69            (k5_xboole_0 @ sk_B_1 @ 
% 0.51/0.69             (k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69              (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))) @ 
% 0.51/0.69            (k4_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69             (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))),
% 0.51/0.69      inference('sup+', [status(thm)], ['38', '45'])).
% 0.51/0.69  thf('47', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.51/0.69           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['25', '26'])).
% 0.51/0.69  thf('48', plain,
% 0.51/0.69      (((k1_tarski @ sk_A)
% 0.51/0.69         = (k5_xboole_0 @ 
% 0.51/0.69            (k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69             (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))) @ 
% 0.51/0.69            (k5_xboole_0 @ sk_B_1 @ 
% 0.51/0.69             (k4_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69              (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))))),
% 0.51/0.69      inference('demod', [status(thm)], ['46', '47'])).
% 0.51/0.69  thf('49', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('demod', [status(thm)], ['42', '43'])).
% 0.51/0.69  thf('50', plain,
% 0.51/0.69      (((k5_xboole_0 @ sk_B_1 @ 
% 0.51/0.69         (k4_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69          (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.51/0.69         = (k5_xboole_0 @ 
% 0.51/0.69            (k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69             (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))) @ 
% 0.51/0.69            (k1_tarski @ sk_A)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['48', '49'])).
% 0.51/0.69  thf('51', plain,
% 0.51/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.69  thf('52', plain,
% 0.51/0.69      (((k5_xboole_0 @ sk_B_1 @ 
% 0.51/0.69         (k4_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69          (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.51/0.69         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.51/0.69            (k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69             (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))),
% 0.51/0.69      inference('demod', [status(thm)], ['50', '51'])).
% 0.51/0.69  thf('53', plain,
% 0.51/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.51/0.69           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.51/0.69  thf('54', plain,
% 0.51/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.69  thf('55', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.51/0.69           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['53', '54'])).
% 0.51/0.69  thf('56', plain,
% 0.51/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.69  thf('57', plain,
% 0.51/0.69      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69         (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.51/0.69         = (k5_xboole_0 @ sk_B_1 @ 
% 0.51/0.69            (k5_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69             (k4_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69              (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))))),
% 0.51/0.69      inference('demod', [status(thm)], ['31', '52', '55', '56'])).
% 0.51/0.69  thf('58', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['39', '44'])).
% 0.51/0.69  thf('59', plain,
% 0.51/0.69      (((sk_B_1)
% 0.51/0.69         = (k5_xboole_0 @ 
% 0.51/0.69            (k5_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69             (k4_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69              (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))) @ 
% 0.51/0.69            (k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69             (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))),
% 0.51/0.69      inference('sup+', [status(thm)], ['57', '58'])).
% 0.51/0.69  thf('60', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.51/0.69           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['25', '26'])).
% 0.51/0.69  thf('61', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.51/0.69           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['53', '54'])).
% 0.51/0.69  thf('62', plain,
% 0.51/0.69      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69         (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.51/0.69         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69            (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))),
% 0.51/0.69      inference('demod', [status(thm)], ['17', '20'])).
% 0.51/0.69  thf('63', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.51/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['33', '34'])).
% 0.51/0.69  thf('64', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['39', '44'])).
% 0.51/0.69  thf('65', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((X1)
% 0.51/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['63', '64'])).
% 0.51/0.69  thf('66', plain,
% 0.51/0.69      (((k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.51/0.69         = (k5_xboole_0 @ 
% 0.51/0.69            (k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69             (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))) @ 
% 0.51/0.69            (k4_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.51/0.69             (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))),
% 0.51/0.69      inference('sup+', [status(thm)], ['62', '65'])).
% 0.51/0.69  thf('67', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.51/0.69           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['53', '54'])).
% 0.51/0.69  thf('68', plain,
% 0.51/0.69      (((sk_B_1)
% 0.51/0.69         = (k5_xboole_0 @ sk_B_1 @ 
% 0.51/0.69            (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.51/0.69             (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))),
% 0.51/0.69      inference('demod', [status(thm)], ['59', '60', '61', '66', '67'])).
% 0.51/0.69  thf('69', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('demod', [status(thm)], ['42', '43'])).
% 0.51/0.69  thf('70', plain,
% 0.51/0.69      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.51/0.69         (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.51/0.69         = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.51/0.69      inference('sup+', [status(thm)], ['68', '69'])).
% 0.51/0.69  thf('71', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.51/0.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.51/0.69  thf('72', plain,
% 0.51/0.69      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.51/0.69         (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))) = (k1_xboole_0))),
% 0.51/0.69      inference('demod', [status(thm)], ['70', '71'])).
% 0.51/0.69  thf('73', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('demod', [status(thm)], ['42', '43'])).
% 0.51/0.69  thf('74', plain,
% 0.51/0.69      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.51/0.69         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['72', '73'])).
% 0.51/0.69  thf('75', plain,
% 0.51/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.69  thf('76', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('77', plain,
% 0.51/0.69      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.51/0.69  thf(d5_xboole_0, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.51/0.69       ( ![D:$i]:
% 0.51/0.69         ( ( r2_hidden @ D @ C ) <=>
% 0.51/0.69           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.51/0.69  thf('78', plain,
% 0.51/0.69      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X8 @ X7)
% 0.51/0.69          | ~ (r2_hidden @ X8 @ X6)
% 0.51/0.69          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.51/0.69      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.51/0.69  thf('79', plain,
% 0.51/0.69      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X8 @ X6)
% 0.51/0.69          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.51/0.69      inference('simplify', [status(thm)], ['78'])).
% 0.51/0.69  thf('80', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.51/0.69          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['77', '79'])).
% 0.51/0.69  thf('81', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.51/0.69      inference('simplify', [status(thm)], ['80'])).
% 0.51/0.69  thf('82', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['0', '81'])).
% 0.51/0.69  thf(t69_enumset1, axiom,
% 0.51/0.69    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.51/0.69  thf('83', plain,
% 0.51/0.69      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.51/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.51/0.69  thf(t20_zfmisc_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.51/0.69         ( k1_tarski @ A ) ) <=>
% 0.51/0.69       ( ( A ) != ( B ) ) ))).
% 0.51/0.69  thf('84', plain,
% 0.51/0.69      (![X51 : $i, X52 : $i]:
% 0.51/0.69         (((X52) != (X51))
% 0.51/0.69          | ((k4_xboole_0 @ (k1_tarski @ X52) @ (k1_tarski @ X51))
% 0.51/0.69              != (k1_tarski @ X52)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.51/0.69  thf('85', plain,
% 0.51/0.69      (![X51 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ (k1_tarski @ X51) @ (k1_tarski @ X51))
% 0.51/0.69           != (k1_tarski @ X51))),
% 0.51/0.69      inference('simplify', [status(thm)], ['84'])).
% 0.51/0.69  thf('86', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.51/0.69           != (k1_tarski @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['83', '85'])).
% 0.51/0.69  thf('87', plain,
% 0.51/0.69      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ k1_xboole_0)
% 0.51/0.69         != (k1_tarski @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['82', '86'])).
% 0.51/0.69  thf('88', plain,
% 0.51/0.69      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.51/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.51/0.69  thf('89', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['0', '81'])).
% 0.51/0.69  thf('90', plain,
% 0.51/0.69      (![X12 : $i, X13 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X12 @ X13)
% 0.51/0.69           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.69  thf('91', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('92', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['90', '91'])).
% 0.51/0.69  thf('93', plain,
% 0.51/0.69      (![X11 : $i]:
% 0.51/0.69         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.51/0.69      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.51/0.69  thf('94', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['90', '91'])).
% 0.51/0.69  thf('95', plain,
% 0.51/0.69      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X8 @ X7)
% 0.51/0.69          | (r2_hidden @ X8 @ X5)
% 0.51/0.69          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.51/0.69      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.51/0.69  thf('96', plain,
% 0.51/0.69      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.51/0.69         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.51/0.69      inference('simplify', [status(thm)], ['95'])).
% 0.51/0.69  thf('97', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.51/0.69          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['94', '96'])).
% 0.51/0.69  thf(idempotence_k3_xboole_0, axiom,
% 0.51/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.51/0.69  thf('98', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 0.51/0.69      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.51/0.69  thf('99', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['90', '91'])).
% 0.51/0.69  thf('100', plain,
% 0.51/0.69      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X8 @ X6)
% 0.51/0.69          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.51/0.69      inference('simplify', [status(thm)], ['78'])).
% 0.51/0.69  thf('101', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.51/0.69          | ~ (r2_hidden @ X1 @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['99', '100'])).
% 0.51/0.69  thf('102', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['98', '101'])).
% 0.51/0.69  thf('103', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.51/0.69      inference('simplify', [status(thm)], ['102'])).
% 0.51/0.69  thf('104', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.69      inference('clc', [status(thm)], ['97', '103'])).
% 0.51/0.69  thf('105', plain,
% 0.51/0.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['93', '104'])).
% 0.51/0.69  thf('106', plain,
% 0.51/0.69      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.51/0.69      inference('demod', [status(thm)], ['92', '105'])).
% 0.51/0.69  thf('107', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['0', '81'])).
% 0.51/0.69  thf('108', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.51/0.69      inference('demod', [status(thm)], ['87', '88', '89', '106', '107'])).
% 0.51/0.69  thf('109', plain, ($false), inference('simplify', [status(thm)], ['108'])).
% 0.51/0.69  
% 0.51/0.69  % SZS output end Refutation
% 0.51/0.69  
% 0.51/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
