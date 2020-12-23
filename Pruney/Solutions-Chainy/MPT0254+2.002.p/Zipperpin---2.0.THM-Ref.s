%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nzXunaj9Dy

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:37 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  141 (2711 expanded)
%              Number of leaves         :   31 ( 944 expanded)
%              Depth                    :   22
%              Number of atoms          :  970 (20775 expanded)
%              Number of equality atoms :  113 (2510 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ X52 @ X53 )
      | ( r2_hidden @ X52 @ X54 )
      | ( X54
       != ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r2_hidden @ X52 @ ( k1_zfmisc_1 @ X53 ) )
      | ~ ( r1_tarski @ X52 @ X53 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k1_zfmisc_1 @ X0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( r2_hidden @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('30',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','35','36','37'])).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
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
    inference('sup+',[status(thm)],['25','26'])).

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
    ( sk_B
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('49',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('64',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('68',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('70',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['46','47','66','67','68','69'])).

thf('71',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['46','47','66','67','68','69'])).

thf('74',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('75',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('77',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['46','47','66','67','68','69'])).

thf('79',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('80',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('82',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('85',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83','84'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('87',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('88',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X57 @ X58 ) )
      = ( k2_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('91',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['89','96'])).

thf('98',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['86','97'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('99',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('100',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['85','100'])).

thf('102',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','101'])).

thf('103',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('105',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['85','100'])).

thf('107',plain,(
    r2_hidden @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['102','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nzXunaj9Dy
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:28:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.75  % Solved by: fo/fo7.sh
% 0.54/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.75  % done 523 iterations in 0.286s
% 0.54/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.75  % SZS output start Refutation
% 0.54/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.75  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.75  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.54/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.75  thf(t1_zfmisc_1, axiom,
% 0.54/0.75    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.54/0.75  thf('0', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.54/0.75  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.75  thf('1', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.75  thf(d1_zfmisc_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.54/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.54/0.75  thf('2', plain,
% 0.54/0.75      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.54/0.75         (~ (r1_tarski @ X52 @ X53)
% 0.54/0.75          | (r2_hidden @ X52 @ X54)
% 0.54/0.75          | ((X54) != (k1_zfmisc_1 @ X53)))),
% 0.54/0.75      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.54/0.75  thf('3', plain,
% 0.54/0.75      (![X52 : $i, X53 : $i]:
% 0.54/0.75         ((r2_hidden @ X52 @ (k1_zfmisc_1 @ X53)) | ~ (r1_tarski @ X52 @ X53))),
% 0.54/0.75      inference('simplify', [status(thm)], ['2'])).
% 0.54/0.75  thf('4', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['1', '3'])).
% 0.54/0.75  thf(antisymmetry_r2_hidden, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.54/0.75  thf('5', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.54/0.75      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.54/0.75  thf('6', plain,
% 0.54/0.75      (![X0 : $i]: ~ (r2_hidden @ (k1_zfmisc_1 @ X0) @ k1_xboole_0)),
% 0.54/0.75      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.75  thf('7', plain, (~ (r2_hidden @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0)),
% 0.54/0.75      inference('sup-', [status(thm)], ['0', '6'])).
% 0.54/0.75  thf(t49_zfmisc_1, conjecture,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.54/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.75    (~( ![A:$i,B:$i]:
% 0.54/0.75        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.54/0.75    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.54/0.75  thf('8', plain,
% 0.54/0.75      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(commutativity_k5_xboole_0, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.54/0.75  thf('9', plain,
% 0.54/0.75      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.75  thf(t94_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( k2_xboole_0 @ A @ B ) =
% 0.54/0.75       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.75  thf('10', plain,
% 0.54/0.75      (![X22 : $i, X23 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X22 @ X23)
% 0.54/0.75           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.54/0.75              (k3_xboole_0 @ X22 @ X23)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.54/0.75  thf('11', plain,
% 0.54/0.75      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.75  thf('12', plain,
% 0.54/0.75      (![X22 : $i, X23 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X22 @ X23)
% 0.54/0.75           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.54/0.75              (k5_xboole_0 @ X22 @ X23)))),
% 0.54/0.75      inference('demod', [status(thm)], ['10', '11'])).
% 0.54/0.75  thf('13', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['9', '12'])).
% 0.54/0.75  thf(commutativity_k3_xboole_0, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.54/0.75  thf('14', plain,
% 0.54/0.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.75  thf('15', plain,
% 0.54/0.75      (![X22 : $i, X23 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X22 @ X23)
% 0.54/0.75           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.54/0.75              (k5_xboole_0 @ X22 @ X23)))),
% 0.54/0.75      inference('demod', [status(thm)], ['10', '11'])).
% 0.54/0.75  thf('16', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['14', '15'])).
% 0.54/0.75  thf('17', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['13', '16'])).
% 0.54/0.75  thf('18', plain,
% 0.54/0.75      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['8', '17'])).
% 0.54/0.75  thf('19', plain,
% 0.54/0.75      (![X22 : $i, X23 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X22 @ X23)
% 0.54/0.75           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.54/0.75              (k5_xboole_0 @ X22 @ X23)))),
% 0.54/0.75      inference('demod', [status(thm)], ['10', '11'])).
% 0.54/0.75  thf('20', plain,
% 0.54/0.75      (![X22 : $i, X23 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X22 @ X23)
% 0.54/0.75           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.54/0.75              (k5_xboole_0 @ X22 @ X23)))),
% 0.54/0.75      inference('demod', [status(thm)], ['10', '11'])).
% 0.54/0.75  thf('21', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.54/0.75           = (k5_xboole_0 @ 
% 0.54/0.75              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.54/0.75              (k2_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['19', '20'])).
% 0.54/0.75  thf('22', plain,
% 0.54/0.75      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.75  thf('23', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.54/0.75           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.54/0.75              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.75  thf('24', plain,
% 0.54/0.75      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.54/0.75         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.54/0.75         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.54/0.75            (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.54/0.75             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.54/0.75      inference('sup+', [status(thm)], ['18', '23'])).
% 0.54/0.75  thf('25', plain,
% 0.54/0.75      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.75  thf(t5_boole, axiom,
% 0.54/0.75    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.75  thf('26', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.54/0.75      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.75  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['25', '26'])).
% 0.54/0.75  thf('28', plain,
% 0.54/0.75      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.54/0.75         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.54/0.75         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.54/0.75            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.54/0.75      inference('demod', [status(thm)], ['24', '27'])).
% 0.54/0.75  thf('29', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['14', '15'])).
% 0.54/0.75  thf('30', plain,
% 0.54/0.75      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.54/0.75         (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.54/0.75         = (k5_xboole_0 @ 
% 0.54/0.75            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.54/0.75             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.54/0.75            (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.54/0.75             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.54/0.75      inference('sup+', [status(thm)], ['28', '29'])).
% 0.54/0.75  thf('31', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['13', '16'])).
% 0.54/0.75  thf(t91_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.54/0.75       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.54/0.75  thf('32', plain,
% 0.54/0.75      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.75         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.54/0.75           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.54/0.75  thf('33', plain,
% 0.54/0.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.75  thf(t100_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.75  thf('34', plain,
% 0.54/0.75      (![X9 : $i, X10 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X9 @ X10)
% 0.54/0.75           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.75  thf('35', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['33', '34'])).
% 0.54/0.75  thf('36', plain,
% 0.54/0.75      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.75  thf('37', plain,
% 0.54/0.75      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.75         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.54/0.75           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.54/0.75  thf('38', plain,
% 0.54/0.75      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.54/0.75         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.54/0.75         = (k5_xboole_0 @ sk_B @ 
% 0.54/0.75            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.54/0.75             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.54/0.75              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.54/0.75      inference('demod', [status(thm)], ['30', '31', '32', '35', '36', '37'])).
% 0.54/0.75  thf('39', plain,
% 0.54/0.75      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.75  thf(t92_xboole_1, axiom,
% 0.54/0.75    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.54/0.75  thf('40', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.75  thf('41', plain,
% 0.54/0.75      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.75         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.54/0.75           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.54/0.75  thf('42', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.54/0.75           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['40', '41'])).
% 0.54/0.75  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['25', '26'])).
% 0.54/0.75  thf('44', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['42', '43'])).
% 0.54/0.75  thf('45', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['39', '44'])).
% 0.54/0.75  thf('46', plain,
% 0.54/0.75      (((sk_B)
% 0.54/0.75         = (k5_xboole_0 @ 
% 0.54/0.75            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.54/0.75             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.54/0.75              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))) @ 
% 0.54/0.75            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.54/0.75             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.54/0.75      inference('sup+', [status(thm)], ['38', '45'])).
% 0.54/0.75  thf('47', plain,
% 0.54/0.75      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.75         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.54/0.75           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.54/0.75  thf(t17_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.54/0.75  thf('48', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 0.54/0.75      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.54/0.75  thf(t3_xboole_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.75  thf('49', plain,
% 0.54/0.75      (![X14 : $i]:
% 0.54/0.75         (((X14) = (k1_xboole_0)) | ~ (r1_tarski @ X14 @ k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.54/0.75  thf('50', plain,
% 0.54/0.75      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['48', '49'])).
% 0.54/0.75  thf('51', plain,
% 0.54/0.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.75  thf('52', plain,
% 0.54/0.75      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['50', '51'])).
% 0.54/0.75  thf('53', plain,
% 0.54/0.75      (![X9 : $i, X10 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X9 @ X10)
% 0.54/0.75           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.75  thf('54', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['52', '53'])).
% 0.54/0.75  thf('55', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.54/0.75      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.75  thf('56', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['54', '55'])).
% 0.54/0.75  thf(t48_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.54/0.75  thf('57', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.54/0.75           = (k3_xboole_0 @ X15 @ X16))),
% 0.54/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.75  thf('58', plain,
% 0.54/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['56', '57'])).
% 0.54/0.75  thf('59', plain,
% 0.54/0.75      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['50', '51'])).
% 0.54/0.75  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['58', '59'])).
% 0.54/0.75  thf('61', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.54/0.75           = (k3_xboole_0 @ X15 @ X16))),
% 0.54/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.75  thf('62', plain,
% 0.54/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['60', '61'])).
% 0.54/0.75  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['54', '55'])).
% 0.54/0.75  thf('64', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['62', '63'])).
% 0.54/0.75  thf('65', plain,
% 0.54/0.75      (![X9 : $i, X10 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X9 @ X10)
% 0.54/0.75           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.75  thf('66', plain,
% 0.54/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['64', '65'])).
% 0.54/0.75  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['58', '59'])).
% 0.54/0.75  thf('68', plain,
% 0.54/0.75      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.75  thf('69', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['25', '26'])).
% 0.54/0.75  thf('70', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['46', '47', '66', '67', '68', '69'])).
% 0.54/0.75  thf('71', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.54/0.75           = (k3_xboole_0 @ X15 @ X16))),
% 0.54/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.75  thf('72', plain,
% 0.54/0.75      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.54/0.75         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['70', '71'])).
% 0.54/0.75  thf('73', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['46', '47', '66', '67', '68', '69'])).
% 0.54/0.75  thf('74', plain,
% 0.54/0.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.75  thf('75', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.54/0.75  thf('76', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['33', '34'])).
% 0.54/0.75  thf('77', plain,
% 0.54/0.75      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.54/0.75         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['75', '76'])).
% 0.54/0.75  thf('78', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['46', '47', '66', '67', '68', '69'])).
% 0.54/0.75  thf('79', plain,
% 0.54/0.75      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.75  thf('80', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.54/0.75  thf('81', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['42', '43'])).
% 0.54/0.75  thf('82', plain, (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['80', '81'])).
% 0.54/0.75  thf('83', plain,
% 0.54/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['64', '65'])).
% 0.54/0.75  thf('84', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['58', '59'])).
% 0.54/0.75  thf('85', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.54/0.75  thf('86', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.54/0.75  thf(t69_enumset1, axiom,
% 0.54/0.75    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.54/0.75  thf('87', plain,
% 0.54/0.75      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.54/0.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.75  thf(l51_zfmisc_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.54/0.75  thf('88', plain,
% 0.54/0.75      (![X57 : $i, X58 : $i]:
% 0.54/0.75         ((k3_tarski @ (k2_tarski @ X57 @ X58)) = (k2_xboole_0 @ X57 @ X58))),
% 0.54/0.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.54/0.75  thf('89', plain,
% 0.54/0.75      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['87', '88'])).
% 0.54/0.75  thf('90', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['62', '63'])).
% 0.54/0.75  thf('91', plain,
% 0.54/0.75      (![X22 : $i, X23 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X22 @ X23)
% 0.54/0.75           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.54/0.75              (k5_xboole_0 @ X22 @ X23)))),
% 0.54/0.75      inference('demod', [status(thm)], ['10', '11'])).
% 0.54/0.75  thf('92', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X0 @ X0)
% 0.54/0.75           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['90', '91'])).
% 0.54/0.75  thf('93', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.75  thf('94', plain,
% 0.54/0.75      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['92', '93'])).
% 0.54/0.75  thf('95', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.54/0.75      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.75  thf('96', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['94', '95'])).
% 0.54/0.75  thf('97', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['89', '96'])).
% 0.54/0.75  thf('98', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.54/0.75      inference('sup+', [status(thm)], ['86', '97'])).
% 0.54/0.75  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.54/0.75  thf('99', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.54/0.75  thf('100', plain, (((sk_A) = (k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['98', '99'])).
% 0.54/0.75  thf('101', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['85', '100'])).
% 0.54/0.75  thf('102', plain, (~ (r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.54/0.75      inference('demod', [status(thm)], ['7', '101'])).
% 0.54/0.75  thf('103', plain,
% 0.54/0.75      (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.54/0.75  thf('104', plain,
% 0.54/0.75      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['1', '3'])).
% 0.54/0.75  thf('105', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['103', '104'])).
% 0.54/0.75  thf('106', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['85', '100'])).
% 0.54/0.75  thf('107', plain, ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.54/0.75      inference('demod', [status(thm)], ['105', '106'])).
% 0.54/0.75  thf('108', plain, ($false), inference('demod', [status(thm)], ['102', '107'])).
% 0.54/0.75  
% 0.54/0.75  % SZS output end Refutation
% 0.54/0.75  
% 0.54/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
