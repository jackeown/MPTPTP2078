%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.el6sBqYZn3

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:45 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 638 expanded)
%              Number of leaves         :   38 ( 225 expanded)
%              Depth                    :   19
%              Number of atoms          : 1120 (4616 expanded)
%              Number of equality atoms :  126 ( 550 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X39 @ X40 )
        = ( k4_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('4',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X22 @ X21 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ X36 )
      | ( r2_hidden @ X35 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X43: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('15',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( r1_tarski @ X31 @ X29 )
      | ( X30
       != ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('17',plain,(
    ! [X29: $i,X31: $i] :
      ( ( r1_tarski @ X31 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['15','17'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','27'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('29',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_A )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','28','44'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('47',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('54',plain,
    ( sk_A
    = ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['47','52','53'])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('56',plain,
    ( ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','68','69'])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['60','70'])).

thf('72',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('81',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('88',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','89'])).

thf('91',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['71','79','90'])).

thf('92',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('95',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('97',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('102',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('105',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['59','95','100','106'])).

thf('108',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('109',plain,(
    ! [X38: $i] :
      ( ( k2_subset_1 @ X38 )
      = X38 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('110',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('112',plain,(
    ! [X41: $i,X42: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('113',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('115',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k4_subset_1 @ X45 @ X44 @ X46 )
        = ( k2_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['110','117'])).

thf('119',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['107','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.el6sBqYZn3
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 494 iterations in 0.159s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.62  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.38/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(t25_subset_1, conjecture,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.62       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.38/0.62         ( k2_subset_1 @ A ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i,B:$i]:
% 0.38/0.62        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.62          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.38/0.62            ( k2_subset_1 @ A ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.38/0.62  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(d5_subset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.62       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (![X39 : $i, X40 : $i]:
% 0.38/0.62         (((k3_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))
% 0.38/0.62          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 0.38/0.62      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.62  thf(d6_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k5_xboole_0 @ A @ B ) =
% 0.38/0.62       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X2 : $i, X3 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ X2 @ X3)
% 0.38/0.62           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.38/0.62      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.38/0.62  thf('4', plain,
% 0.38/0.62      (((k5_xboole_0 @ sk_B @ sk_A)
% 0.38/0.62         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 0.38/0.62            (k3_subset_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.62  thf(commutativity_k2_tarski, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (![X21 : $i, X22 : $i]:
% 0.38/0.62         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.62  thf(l51_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      (![X33 : $i, X34 : $i]:
% 0.38/0.62         ((k3_tarski @ (k2_tarski @ X33 @ X34)) = (k2_xboole_0 @ X33 @ X34))),
% 0.38/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.62  thf('7', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (![X33 : $i, X34 : $i]:
% 0.38/0.62         ((k3_tarski @ (k2_tarski @ X33 @ X34)) = (k2_xboole_0 @ X33 @ X34))),
% 0.38/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.62  thf('9', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (((k5_xboole_0 @ sk_B @ sk_A)
% 0.38/0.62         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.38/0.62            (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['4', '9'])).
% 0.38/0.62  thf('11', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(d2_subset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( v1_xboole_0 @ A ) =>
% 0.38/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.38/0.62       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      (![X35 : $i, X36 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X35 @ X36)
% 0.38/0.62          | (r2_hidden @ X35 @ X36)
% 0.38/0.62          | (v1_xboole_0 @ X36))),
% 0.38/0.62      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.38/0.62        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.62  thf(fc1_subset_1, axiom,
% 0.38/0.62    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.62  thf('14', plain, (![X43 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X43))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.38/0.62  thf('15', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['13', '14'])).
% 0.38/0.62  thf(d1_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.38/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X31 @ X30)
% 0.38/0.62          | (r1_tarski @ X31 @ X29)
% 0.38/0.62          | ((X30) != (k1_zfmisc_1 @ X29)))),
% 0.38/0.62      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      (![X29 : $i, X31 : $i]:
% 0.38/0.62         ((r1_tarski @ X31 @ X29) | ~ (r2_hidden @ X31 @ (k1_zfmisc_1 @ X29)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.62  thf('18', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['15', '17'])).
% 0.38/0.62  thf(t28_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      (![X12 : $i, X13 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.38/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.62  thf('20', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.62  thf(t22_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (![X10 : $i, X11 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.38/0.62      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['21', '22'])).
% 0.38/0.62  thf('24', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf(t46_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (![X14 : $i, X15 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['24', '25'])).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['23', '26'])).
% 0.38/0.62  thf('28', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['20', '27'])).
% 0.38/0.62  thf(idempotence_k3_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.38/0.62  thf('29', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      (![X10 : $i, X11 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.38/0.62      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.38/0.62  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['29', '30'])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      (![X14 : $i, X15 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.38/0.62  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      (![X2 : $i, X3 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ X2 @ X3)
% 0.38/0.62           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.38/0.62      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.38/0.62  thf('35', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ X0 @ X0)
% 0.38/0.62           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['33', '34'])).
% 0.38/0.62  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.38/0.62  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['29', '30'])).
% 0.38/0.62  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.38/0.62  thf(t112_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.38/0.62       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.38/0.62  thf('39', plain,
% 0.38/0.62      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 0.38/0.62           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 0.38/0.62      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.38/0.62  thf('40', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k1_xboole_0) = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['38', '39'])).
% 0.38/0.62  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.38/0.62  thf('42', plain,
% 0.38/0.62      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['40', '41'])).
% 0.38/0.62  thf('43', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['21', '22'])).
% 0.38/0.62  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['42', '43'])).
% 0.38/0.62  thf('45', plain,
% 0.38/0.62      (((k5_xboole_0 @ sk_B @ sk_A) = (k3_subset_1 @ sk_A @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['10', '28', '44'])).
% 0.38/0.62  thf(t94_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k2_xboole_0 @ A @ B ) =
% 0.38/0.62       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.62  thf('46', plain,
% 0.38/0.62      (![X19 : $i, X20 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X19 @ X20)
% 0.38/0.62           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 0.38/0.62              (k3_xboole_0 @ X19 @ X20)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.38/0.62  thf('47', plain,
% 0.38/0.62      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.38/0.62         = (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.38/0.62            (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['45', '46'])).
% 0.38/0.62  thf('48', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.62  thf('49', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['21', '22'])).
% 0.38/0.62  thf('50', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.38/0.62      inference('sup+', [status(thm)], ['48', '49'])).
% 0.38/0.62  thf('51', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf('52', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['50', '51'])).
% 0.38/0.62  thf('53', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.62  thf('54', plain,
% 0.38/0.62      (((sk_A) = (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['47', '52', '53'])).
% 0.38/0.62  thf('55', plain,
% 0.38/0.62      (![X19 : $i, X20 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X19 @ X20)
% 0.38/0.62           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 0.38/0.62              (k3_xboole_0 @ X19 @ X20)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.38/0.62  thf('56', plain,
% 0.38/0.62      (((k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.38/0.62         = (k5_xboole_0 @ sk_A @ 
% 0.38/0.62            (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['54', '55'])).
% 0.38/0.62  thf('57', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf('58', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.62  thf('59', plain,
% 0.38/0.62      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.38/0.62         = (k5_xboole_0 @ sk_A @ 
% 0.38/0.62            (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.38/0.62  thf('60', plain,
% 0.38/0.62      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.38/0.62         = (k5_xboole_0 @ sk_A @ 
% 0.38/0.62            (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.38/0.62  thf('61', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.62  thf('62', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.62  thf('63', plain,
% 0.38/0.62      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 0.38/0.62           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 0.38/0.62      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.38/0.62  thf('64', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 0.38/0.62           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['62', '63'])).
% 0.38/0.62  thf('65', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 0.38/0.62           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.38/0.62      inference('sup+', [status(thm)], ['61', '64'])).
% 0.38/0.62  thf('66', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.62  thf(t100_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.62  thf('67', plain,
% 0.38/0.62      (![X5 : $i, X6 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X5 @ X6)
% 0.38/0.62           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.62  thf('68', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.62           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['66', '67'])).
% 0.38/0.62  thf('69', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.62  thf('70', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ sk_B @ X0)
% 0.38/0.62           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['65', '68', '69'])).
% 0.38/0.62  thf('71', plain,
% 0.38/0.62      (((k4_xboole_0 @ sk_B @ 
% 0.38/0.62         (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.38/0.62         = (k3_xboole_0 @ sk_B @ 
% 0.38/0.62            (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('sup+', [status(thm)], ['60', '70'])).
% 0.38/0.62  thf('72', plain,
% 0.38/0.62      (![X10 : $i, X11 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.38/0.62      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.38/0.62  thf('73', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['24', '25'])).
% 0.38/0.62  thf('74', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['72', '73'])).
% 0.38/0.62  thf('75', plain,
% 0.38/0.62      (![X2 : $i, X3 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ X2 @ X3)
% 0.38/0.62           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.38/0.62      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.38/0.62  thf('76', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.38/0.62           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.38/0.62              k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['74', '75'])).
% 0.38/0.62  thf('77', plain,
% 0.38/0.62      (![X5 : $i, X6 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X5 @ X6)
% 0.38/0.62           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.62  thf('78', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['42', '43'])).
% 0.38/0.62  thf('79', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.62           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.62      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.38/0.62  thf('80', plain,
% 0.38/0.62      (![X14 : $i, X15 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.38/0.62  thf(t48_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.62  thf('81', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.38/0.62           = (k3_xboole_0 @ X16 @ X17))),
% 0.38/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.62  thf('82', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.38/0.62           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['80', '81'])).
% 0.38/0.62  thf('83', plain,
% 0.38/0.62      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['40', '41'])).
% 0.38/0.62  thf('84', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.62  thf('85', plain,
% 0.38/0.62      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['83', '84'])).
% 0.38/0.62  thf('86', plain,
% 0.38/0.62      (![X5 : $i, X6 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X5 @ X6)
% 0.38/0.62           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.62  thf('87', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['85', '86'])).
% 0.38/0.62  thf(t5_boole, axiom,
% 0.38/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.62  thf('88', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.38/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.62  thf('89', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['87', '88'])).
% 0.38/0.62  thf('90', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['82', '89'])).
% 0.38/0.62  thf('91', plain,
% 0.38/0.62      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['71', '79', '90'])).
% 0.38/0.62  thf('92', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.38/0.62           = (k3_xboole_0 @ X16 @ X17))),
% 0.38/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.62  thf('93', plain,
% 0.38/0.62      (((k4_xboole_0 @ sk_B @ sk_B)
% 0.38/0.62         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['91', '92'])).
% 0.38/0.62  thf('94', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.38/0.62  thf('95', plain,
% 0.38/0.62      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('demod', [status(thm)], ['93', '94'])).
% 0.38/0.62  thf('96', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf('97', plain,
% 0.38/0.62      (![X2 : $i, X3 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ X2 @ X3)
% 0.38/0.62           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.38/0.62      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.38/0.62  thf('98', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ X1 @ X0)
% 0.38/0.62           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['96', '97'])).
% 0.38/0.62  thf('99', plain,
% 0.38/0.62      (![X2 : $i, X3 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ X2 @ X3)
% 0.38/0.62           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.38/0.62      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.38/0.62  thf('100', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['98', '99'])).
% 0.38/0.62  thf('101', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.38/0.62  thf('102', plain,
% 0.38/0.62      (![X19 : $i, X20 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X19 @ X20)
% 0.38/0.62           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 0.38/0.62              (k3_xboole_0 @ X19 @ X20)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.38/0.62  thf('103', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X0 @ X0)
% 0.38/0.62           = (k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['101', '102'])).
% 0.38/0.62  thf('104', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['29', '30'])).
% 0.38/0.62  thf('105', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.38/0.62  thf('106', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.38/0.62  thf('107', plain,
% 0.38/0.62      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['59', '95', '100', '106'])).
% 0.38/0.62  thf('108', plain,
% 0.38/0.62      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.38/0.62         != (k2_subset_1 @ sk_A))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.38/0.62  thf('109', plain, (![X38 : $i]: ((k2_subset_1 @ X38) = (X38))),
% 0.38/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.62  thf('110', plain,
% 0.38/0.62      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['108', '109'])).
% 0.38/0.62  thf('111', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(dt_k3_subset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.62       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.62  thf('112', plain,
% 0.38/0.62      (![X41 : $i, X42 : $i]:
% 0.38/0.62         ((m1_subset_1 @ (k3_subset_1 @ X41 @ X42) @ (k1_zfmisc_1 @ X41))
% 0.38/0.62          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.38/0.62  thf('113', plain,
% 0.38/0.62      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['111', '112'])).
% 0.38/0.62  thf('114', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(redefinition_k4_subset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.38/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.62       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.62  thf('115', plain,
% 0.38/0.62      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.38/0.62          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45))
% 0.38/0.62          | ((k4_subset_1 @ X45 @ X44 @ X46) = (k2_xboole_0 @ X44 @ X46)))),
% 0.38/0.62      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.38/0.62  thf('116', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.38/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.38/0.62  thf('117', plain,
% 0.38/0.62      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.38/0.62         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['113', '116'])).
% 0.38/0.62  thf('118', plain,
% 0.38/0.62      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['110', '117'])).
% 0.38/0.62  thf('119', plain, ($false),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['107', '118'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
