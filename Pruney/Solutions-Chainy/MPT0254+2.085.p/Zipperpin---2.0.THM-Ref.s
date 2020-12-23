%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gDYrEW34MF

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:46 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  133 (1483 expanded)
%              Number of leaves         :   35 ( 538 expanded)
%              Depth                    :   20
%              Number of atoms          :  913 (12157 expanded)
%              Number of equality atoms :   98 (1407 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( r1_tarski @ X55 @ X56 )
      | ( r2_hidden @ X55 @ X57 )
      | ( X57
       != ( k1_zfmisc_1 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r2_hidden @ X55 @ ( k1_zfmisc_1 @ X56 ) )
      | ~ ( r1_tarski @ X55 @ X56 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
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

thf('11',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27','30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('33',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','39','40','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('44',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('56',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('60',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['50','51','54','57','58','59'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['50','51','54','57','58','59'])).

thf('69',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('71',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['50','51','54','57','58','59'])).

thf('73',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('74',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('76',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('79',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77','78'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('81',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('82',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X60 @ X61 ) )
      = ( k2_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('84',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['80','85'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('87',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('88',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['79','88'])).

thf('90',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['79','88'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('91',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('92',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['14','89','90','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gDYrEW34MF
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.69  % Solved by: fo/fo7.sh
% 0.46/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.69  % done 542 iterations in 0.236s
% 0.46/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.69  % SZS output start Refutation
% 0.46/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.69  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.69  thf(t1_zfmisc_1, axiom,
% 0.46/0.69    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.46/0.69  thf('0', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.46/0.69      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.46/0.69  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.69  thf('1', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 0.46/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.69  thf(d1_zfmisc_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.46/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.46/0.69  thf('2', plain,
% 0.46/0.69      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.46/0.69         (~ (r1_tarski @ X55 @ X56)
% 0.46/0.69          | (r2_hidden @ X55 @ X57)
% 0.46/0.69          | ((X57) != (k1_zfmisc_1 @ X56)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.69  thf('3', plain,
% 0.46/0.69      (![X55 : $i, X56 : $i]:
% 0.46/0.69         ((r2_hidden @ X55 @ (k1_zfmisc_1 @ X56)) | ~ (r1_tarski @ X55 @ X56))),
% 0.46/0.69      inference('simplify', [status(thm)], ['2'])).
% 0.46/0.69  thf('4', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['1', '3'])).
% 0.46/0.69  thf('5', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['0', '4'])).
% 0.46/0.69  thf(d10_xboole_0, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.69  thf('6', plain,
% 0.46/0.69      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.69  thf('7', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.46/0.69      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.69  thf(t28_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.69  thf('8', plain,
% 0.46/0.69      (![X14 : $i, X15 : $i]:
% 0.46/0.69         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.46/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.69  thf('9', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.69  thf('10', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.69  thf(t4_xboole_0, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.69            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.69  thf('11', plain,
% 0.46/0.69      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.46/0.69          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.46/0.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.69  thf('12', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.69          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.69  thf('13', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['9', '12'])).
% 0.46/0.69  thf('14', plain,
% 0.46/0.69      (~ (r1_xboole_0 @ (k1_tarski @ k1_xboole_0) @ (k1_tarski @ k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['5', '13'])).
% 0.46/0.69  thf(t49_zfmisc_1, conjecture,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.46/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.69    (~( ![A:$i,B:$i]:
% 0.46/0.69        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.46/0.69    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.46/0.69  thf('15', plain,
% 0.46/0.69      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(t94_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( k2_xboole_0 @ A @ B ) =
% 0.46/0.69       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.69  thf('16', plain,
% 0.46/0.69      (![X25 : $i, X26 : $i]:
% 0.46/0.69         ((k2_xboole_0 @ X25 @ X26)
% 0.46/0.69           = (k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ 
% 0.46/0.69              (k3_xboole_0 @ X25 @ X26)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.46/0.69  thf(commutativity_k5_xboole_0, axiom,
% 0.46/0.69    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.46/0.69  thf('17', plain,
% 0.46/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.69  thf('18', plain,
% 0.46/0.69      (![X25 : $i, X26 : $i]:
% 0.46/0.69         ((k2_xboole_0 @ X25 @ X26)
% 0.46/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ 
% 0.46/0.69              (k5_xboole_0 @ X25 @ X26)))),
% 0.46/0.69      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.69  thf('19', plain,
% 0.46/0.69      (![X25 : $i, X26 : $i]:
% 0.46/0.69         ((k2_xboole_0 @ X25 @ X26)
% 0.46/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ 
% 0.46/0.69              (k5_xboole_0 @ X25 @ X26)))),
% 0.46/0.69      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.69  thf('20', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.46/0.69           = (k5_xboole_0 @ 
% 0.46/0.69              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.46/0.69              (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.46/0.69  thf('21', plain,
% 0.46/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.69  thf('22', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.46/0.69           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.46/0.69              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.46/0.69      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.69  thf('23', plain,
% 0.46/0.69      (((k2_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.46/0.69         (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.46/0.69         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.69            (k3_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.46/0.69             (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))),
% 0.46/0.69      inference('sup+', [status(thm)], ['15', '22'])).
% 0.46/0.69  thf('24', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.69  thf('25', plain,
% 0.46/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.69  thf('26', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.69  thf('27', plain,
% 0.46/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.69  thf('28', plain,
% 0.46/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.69  thf(t5_boole, axiom,
% 0.46/0.69    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.69  thf('29', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.46/0.69      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.69  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.69  thf('31', plain,
% 0.46/0.69      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.69         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.69         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.69            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.46/0.69      inference('demod', [status(thm)], ['23', '24', '25', '26', '27', '30'])).
% 0.46/0.69  thf('32', plain,
% 0.46/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.69  thf('33', plain,
% 0.46/0.69      (![X25 : $i, X26 : $i]:
% 0.46/0.69         ((k2_xboole_0 @ X25 @ X26)
% 0.46/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ 
% 0.46/0.69              (k5_xboole_0 @ X25 @ X26)))),
% 0.46/0.69      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.69  thf('34', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['32', '33'])).
% 0.46/0.69  thf('35', plain,
% 0.46/0.69      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.69         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.69         = (k5_xboole_0 @ 
% 0.46/0.69            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.69             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.46/0.69            (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.69             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.46/0.69      inference('sup+', [status(thm)], ['31', '34'])).
% 0.46/0.69  thf(t91_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.69       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.46/0.69  thf('36', plain,
% 0.46/0.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.69           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.69  thf('37', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.69  thf(t100_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.69  thf('38', plain,
% 0.46/0.69      (![X12 : $i, X13 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X12 @ X13)
% 0.46/0.70           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.70  thf('39', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.70           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['37', '38'])).
% 0.46/0.70  thf('40', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.70  thf('41', plain,
% 0.46/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.70         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.70           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.70  thf('42', plain,
% 0.46/0.70      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.70         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.70         = (k5_xboole_0 @ sk_B @ 
% 0.46/0.70            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.46/0.70             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.70              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.46/0.70      inference('demod', [status(thm)], ['35', '36', '39', '40', '41'])).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.70  thf(t92_xboole_1, axiom,
% 0.46/0.70    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.70  thf('44', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.70  thf('45', plain,
% 0.46/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.70         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.70           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.70  thf('46', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.70           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['44', '45'])).
% 0.46/0.70  thf('47', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.70  thf('48', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.70  thf('49', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['43', '48'])).
% 0.46/0.70  thf('50', plain,
% 0.46/0.70      (((sk_B)
% 0.46/0.70         = (k5_xboole_0 @ 
% 0.46/0.70            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.46/0.70             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.70              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))) @ 
% 0.46/0.70            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.70             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['42', '49'])).
% 0.46/0.70  thf('51', plain,
% 0.46/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.70         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.70           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.70  thf('52', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.70  thf('53', plain,
% 0.46/0.70      (![X12 : $i, X13 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X12 @ X13)
% 0.46/0.70           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.70  thf('54', plain,
% 0.46/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.70  thf('56', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.70  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['55', '56'])).
% 0.46/0.70  thf('58', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.70  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.70  thf('60', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['50', '51', '54', '57', '58', '59'])).
% 0.46/0.70  thf(t36_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.70  thf('61', plain,
% 0.46/0.70      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 0.46/0.70      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.46/0.70  thf('62', plain,
% 0.46/0.70      (![X14 : $i, X15 : $i]:
% 0.46/0.70         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.70  thf('63', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.46/0.70           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.70  thf('64', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.70  thf('65', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.46/0.70           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('demod', [status(thm)], ['63', '64'])).
% 0.46/0.70  thf('66', plain,
% 0.46/0.70      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.70         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['60', '65'])).
% 0.46/0.70  thf('67', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.70  thf('68', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['50', '51', '54', '57', '58', '59'])).
% 0.46/0.70  thf('69', plain, (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.46/0.70  thf('70', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.70           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['37', '38'])).
% 0.46/0.70  thf('71', plain,
% 0.46/0.70      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.70         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['69', '70'])).
% 0.46/0.70  thf('72', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['50', '51', '54', '57', '58', '59'])).
% 0.46/0.70  thf('73', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.70  thf('74', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.46/0.70  thf('75', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.70  thf('76', plain, (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['74', '75'])).
% 0.46/0.70  thf('77', plain,
% 0.46/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.70  thf('78', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['55', '56'])).
% 0.46/0.70  thf('79', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.46/0.70      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.46/0.70  thf('80', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.46/0.70      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.46/0.70  thf(t69_enumset1, axiom,
% 0.46/0.70    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.70  thf('81', plain,
% 0.46/0.70      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.46/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.70  thf(l51_zfmisc_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.70  thf('82', plain,
% 0.46/0.70      (![X60 : $i, X61 : $i]:
% 0.46/0.70         ((k3_tarski @ (k2_tarski @ X60 @ X61)) = (k2_xboole_0 @ X60 @ X61))),
% 0.46/0.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.70  thf('83', plain,
% 0.46/0.70      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['81', '82'])).
% 0.46/0.70  thf(idempotence_k2_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.70  thf('84', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.46/0.70  thf('85', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['83', '84'])).
% 0.46/0.70  thf('86', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.46/0.70      inference('sup+', [status(thm)], ['80', '85'])).
% 0.46/0.70  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.46/0.70  thf('87', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.46/0.70  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['86', '87'])).
% 0.46/0.70  thf('89', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.70      inference('demod', [status(thm)], ['79', '88'])).
% 0.46/0.70  thf('90', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.70      inference('demod', [status(thm)], ['79', '88'])).
% 0.46/0.70  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.46/0.70  thf('91', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 0.46/0.70      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.46/0.70  thf('92', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i]:
% 0.46/0.70         ((r1_xboole_0 @ X5 @ X6)
% 0.46/0.70          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.70  thf('93', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.70          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.70  thf('94', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['92', '93'])).
% 0.46/0.70  thf('95', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.70      inference('sup-', [status(thm)], ['91', '94'])).
% 0.46/0.70  thf('96', plain, ($false),
% 0.46/0.70      inference('demod', [status(thm)], ['14', '89', '90', '95'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.54/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
