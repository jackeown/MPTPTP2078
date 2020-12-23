%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J0tSM8Qwod

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:51 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 196 expanded)
%              Number of leaves         :   39 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          : 1013 (1725 expanded)
%              Number of equality atoms :   90 ( 154 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X66 @ X67 )
      | ( r2_hidden @ X66 @ X67 )
      | ( v1_xboole_0 @ X67 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X74: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X74 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( r2_hidden @ X62 @ X61 )
      | ( r1_tarski @ X62 @ X60 )
      | ( X61
       != ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X60: $i,X62: $i] :
      ( ( r1_tarski @ X62 @ X60 )
      | ~ ( r2_hidden @ X62 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
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

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X70: $i,X71: $i] :
      ( ( ( k3_subset_1 @ X70 @ X71 )
        = ( k4_xboole_0 @ X70 @ X71 ) )
      | ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['19'])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['19'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('31',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( X13
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ X14 @ X11 )
      | ( X13
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ X14 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','43'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ X29 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('48',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['18','50'])).

thf('52',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('55',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('59',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('62',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('68',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('71',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('72',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X30 @ X31 ) @ ( k3_xboole_0 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('73',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('74',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ X29 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('76',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) )
      = ( k5_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf('78',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['51','77'])).

thf('79',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('80',plain,(
    ! [X69: $i] :
      ( ( k2_subset_1 @ X69 )
      = X69 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('81',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
 != sk_A ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('83',plain,(
    ! [X72: $i,X73: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X72 @ X73 ) @ ( k1_zfmisc_1 @ X72 ) )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ X72 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('84',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('86',plain,(
    ! [X75: $i,X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X75 @ ( k1_zfmisc_1 @ X76 ) )
      | ~ ( m1_subset_1 @ X77 @ ( k1_zfmisc_1 @ X76 ) )
      | ( ( k4_subset_1 @ X76 @ X75 @ X77 )
        = ( k2_xboole_0 @ X75 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('87',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('88',plain,(
    ! [X75: $i,X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X75 @ ( k1_zfmisc_1 @ X76 ) )
      | ~ ( m1_subset_1 @ X77 @ ( k1_zfmisc_1 @ X76 ) )
      | ( ( k4_subset_1 @ X76 @ X75 @ X77 )
        = ( k3_tarski @ ( k2_tarski @ X75 @ X77 ) ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['81','90'])).

thf('92',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['78','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J0tSM8Qwod
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.87  % Solved by: fo/fo7.sh
% 0.68/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.87  % done 538 iterations in 0.368s
% 0.68/0.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.87  % SZS output start Refutation
% 0.68/0.87  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.87  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.68/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.87  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.68/0.87  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.68/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.87  thf(sk_B_type, type, sk_B: $i > $i).
% 0.68/0.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.87  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.68/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.68/0.87  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.68/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.87  thf(t25_subset_1, conjecture,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.87       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.68/0.87         ( k2_subset_1 @ A ) ) ))).
% 0.68/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.87    (~( ![A:$i,B:$i]:
% 0.68/0.87        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.87          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.68/0.87            ( k2_subset_1 @ A ) ) ) )),
% 0.68/0.87    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.68/0.87  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(d2_subset_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( v1_xboole_0 @ A ) =>
% 0.68/0.87         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.68/0.87       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.68/0.87         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.68/0.87  thf('1', plain,
% 0.68/0.87      (![X66 : $i, X67 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X66 @ X67)
% 0.68/0.87          | (r2_hidden @ X66 @ X67)
% 0.68/0.87          | (v1_xboole_0 @ X67))),
% 0.68/0.87      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.68/0.87  thf('2', plain,
% 0.68/0.87      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.68/0.87        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['0', '1'])).
% 0.68/0.87  thf(fc1_subset_1, axiom,
% 0.68/0.87    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.68/0.87  thf('3', plain, (![X74 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X74))),
% 0.68/0.87      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.68/0.87  thf('4', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.87      inference('clc', [status(thm)], ['2', '3'])).
% 0.68/0.87  thf(d1_zfmisc_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.68/0.87       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.68/0.87  thf('5', plain,
% 0.68/0.87      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X62 @ X61)
% 0.68/0.87          | (r1_tarski @ X62 @ X60)
% 0.68/0.87          | ((X61) != (k1_zfmisc_1 @ X60)))),
% 0.68/0.87      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.68/0.87  thf('6', plain,
% 0.68/0.87      (![X60 : $i, X62 : $i]:
% 0.68/0.87         ((r1_tarski @ X62 @ X60) | ~ (r2_hidden @ X62 @ (k1_zfmisc_1 @ X60)))),
% 0.68/0.87      inference('simplify', [status(thm)], ['5'])).
% 0.68/0.87  thf('7', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.68/0.87      inference('sup-', [status(thm)], ['4', '6'])).
% 0.68/0.87  thf(t28_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.68/0.87  thf('8', plain,
% 0.68/0.87      (![X22 : $i, X23 : $i]:
% 0.68/0.87         (((k3_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_tarski @ X22 @ X23))),
% 0.68/0.87      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.68/0.87  thf('9', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['7', '8'])).
% 0.68/0.87  thf(commutativity_k3_xboole_0, axiom,
% 0.68/0.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.68/0.87  thf('10', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.87  thf(t100_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.68/0.87  thf('11', plain,
% 0.68/0.87      (![X17 : $i, X18 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ X17 @ X18)
% 0.68/0.87           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.87  thf('12', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ X0 @ X1)
% 0.68/0.87           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['10', '11'])).
% 0.68/0.87  thf('13', plain,
% 0.68/0.87      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.68/0.87      inference('sup+', [status(thm)], ['9', '12'])).
% 0.68/0.87  thf('14', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(d5_subset_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.87       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.68/0.87  thf('15', plain,
% 0.68/0.87      (![X70 : $i, X71 : $i]:
% 0.68/0.87         (((k3_subset_1 @ X70 @ X71) = (k4_xboole_0 @ X70 @ X71))
% 0.68/0.87          | ~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ X70)))),
% 0.68/0.87      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.68/0.87  thf('16', plain,
% 0.68/0.87      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.87  thf(commutativity_k5_xboole_0, axiom,
% 0.68/0.87    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.68/0.87  thf('17', plain,
% 0.68/0.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.68/0.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.68/0.87  thf('18', plain,
% 0.68/0.87      (((k3_subset_1 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_B_1 @ sk_A))),
% 0.68/0.87      inference('demod', [status(thm)], ['13', '16', '17'])).
% 0.68/0.87  thf(d4_xboole_0, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.68/0.87       ( ![D:$i]:
% 0.68/0.87         ( ( r2_hidden @ D @ C ) <=>
% 0.68/0.87           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.68/0.87  thf('19', plain,
% 0.68/0.87      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.68/0.87         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.68/0.87          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.68/0.87          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.68/0.87      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.68/0.87  thf('20', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.68/0.87          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.87      inference('eq_fact', [status(thm)], ['19'])).
% 0.68/0.87  thf('21', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.68/0.87          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.87      inference('eq_fact', [status(thm)], ['19'])).
% 0.68/0.87  thf('22', plain,
% 0.68/0.87      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.68/0.87         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.68/0.87          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.68/0.87          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.68/0.87          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.68/0.87      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.68/0.87  thf('23', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.68/0.87          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.68/0.87          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.68/0.87          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['21', '22'])).
% 0.68/0.87  thf('24', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.68/0.87          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.68/0.87          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.87      inference('simplify', [status(thm)], ['23'])).
% 0.68/0.87  thf('25', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.68/0.87          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.87      inference('eq_fact', [status(thm)], ['19'])).
% 0.68/0.87  thf('26', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.68/0.87          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.68/0.87      inference('clc', [status(thm)], ['24', '25'])).
% 0.68/0.87  thf('27', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         (((X0) = (k3_xboole_0 @ X0 @ X0)) | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['20', '26'])).
% 0.68/0.87  thf('28', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.68/0.87      inference('simplify', [status(thm)], ['27'])).
% 0.68/0.87  thf('29', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ X0 @ X1)
% 0.68/0.87           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['10', '11'])).
% 0.68/0.87  thf('30', plain,
% 0.68/0.87      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['28', '29'])).
% 0.68/0.87  thf(t7_xboole_0, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.68/0.87          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.68/0.87  thf('31', plain,
% 0.68/0.87      (![X16 : $i]:
% 0.68/0.87         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 0.68/0.87      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.68/0.87  thf('32', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.68/0.87      inference('simplify', [status(thm)], ['27'])).
% 0.68/0.87  thf('33', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.87  thf(t48_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.68/0.87  thf('34', plain,
% 0.68/0.87      (![X24 : $i, X25 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.68/0.87           = (k3_xboole_0 @ X24 @ X25))),
% 0.68/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.87  thf(d5_xboole_0, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.68/0.87       ( ![D:$i]:
% 0.68/0.87         ( ( r2_hidden @ D @ C ) <=>
% 0.68/0.87           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.68/0.87  thf('35', plain,
% 0.68/0.87      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X14 @ X13)
% 0.68/0.87          | ~ (r2_hidden @ X14 @ X12)
% 0.68/0.87          | ((X13) != (k4_xboole_0 @ X11 @ X12)))),
% 0.68/0.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.68/0.87  thf('36', plain,
% 0.68/0.87      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X14 @ X12)
% 0.68/0.87          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 0.68/0.87      inference('simplify', [status(thm)], ['35'])).
% 0.68/0.87  thf('37', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.87          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['34', '36'])).
% 0.68/0.87  thf('38', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.87          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['33', '37'])).
% 0.68/0.87  thf('39', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X1 @ X0)
% 0.68/0.87          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['32', '38'])).
% 0.68/0.87  thf('40', plain,
% 0.68/0.87      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X14 @ X13)
% 0.68/0.87          | (r2_hidden @ X14 @ X11)
% 0.68/0.87          | ((X13) != (k4_xboole_0 @ X11 @ X12)))),
% 0.68/0.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.68/0.87  thf('41', plain,
% 0.68/0.87      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.68/0.87         ((r2_hidden @ X14 @ X11)
% 0.68/0.87          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 0.68/0.87      inference('simplify', [status(thm)], ['40'])).
% 0.68/0.87  thf('42', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.68/0.87      inference('clc', [status(thm)], ['39', '41'])).
% 0.68/0.87  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.87      inference('sup-', [status(thm)], ['31', '42'])).
% 0.68/0.87  thf('44', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.68/0.87      inference('demod', [status(thm)], ['30', '43'])).
% 0.68/0.87  thf(t91_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.68/0.87       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.68/0.87  thf('45', plain,
% 0.68/0.87      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.68/0.87         ((k5_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ X29)
% 0.68/0.87           = (k5_xboole_0 @ X27 @ (k5_xboole_0 @ X28 @ X29)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.68/0.87  thf('46', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.68/0.87           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['44', '45'])).
% 0.68/0.87  thf('47', plain,
% 0.68/0.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.68/0.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.68/0.87  thf(t5_boole, axiom,
% 0.68/0.87    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.68/0.87  thf('48', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 0.68/0.87      inference('cnf', [status(esa)], [t5_boole])).
% 0.68/0.87  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['47', '48'])).
% 0.68/0.87  thf('50', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.68/0.87      inference('demod', [status(thm)], ['46', '49'])).
% 0.68/0.87  thf('51', plain,
% 0.68/0.87      (((sk_A) = (k5_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['18', '50'])).
% 0.68/0.87  thf('52', plain,
% 0.68/0.87      (![X16 : $i]:
% 0.68/0.87         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 0.68/0.87      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.68/0.87  thf('53', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.87  thf('54', plain,
% 0.68/0.87      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X8 @ X7)
% 0.68/0.87          | (r2_hidden @ X8 @ X6)
% 0.68/0.87          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.68/0.87      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.68/0.87  thf('55', plain,
% 0.68/0.87      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.68/0.87         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.68/0.87      inference('simplify', [status(thm)], ['54'])).
% 0.68/0.87  thf('56', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['53', '55'])).
% 0.68/0.87  thf('57', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.68/0.87          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['52', '56'])).
% 0.68/0.87  thf('58', plain,
% 0.68/0.87      (![X16 : $i]:
% 0.68/0.87         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 0.68/0.87      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.68/0.87  thf('59', plain,
% 0.68/0.87      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.68/0.87         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.68/0.87      inference('simplify', [status(thm)], ['54'])).
% 0.68/0.87  thf('60', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.68/0.87          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.68/0.87      inference('sup-', [status(thm)], ['58', '59'])).
% 0.68/0.87  thf('61', plain,
% 0.68/0.87      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.87  thf('62', plain,
% 0.68/0.87      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X14 @ X12)
% 0.68/0.87          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 0.68/0.87      inference('simplify', [status(thm)], ['35'])).
% 0.68/0.87  thf('63', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.68/0.87          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['61', '62'])).
% 0.68/0.87  thf('64', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         (((k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))
% 0.68/0.87          | ~ (r2_hidden @ 
% 0.68/0.87               (sk_B @ (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))) @ 
% 0.68/0.87               sk_B_1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['60', '63'])).
% 0.68/0.87  thf('65', plain,
% 0.68/0.87      ((((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))
% 0.68/0.87        | ((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.68/0.87            = (k1_xboole_0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['57', '64'])).
% 0.68/0.87  thf('66', plain,
% 0.68/0.87      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.68/0.87      inference('simplify', [status(thm)], ['65'])).
% 0.68/0.87  thf('67', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ X0 @ X1)
% 0.68/0.87           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['10', '11'])).
% 0.68/0.87  thf('68', plain,
% 0.68/0.87      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.68/0.87         = (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ k1_xboole_0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['66', '67'])).
% 0.68/0.87  thf('69', plain,
% 0.68/0.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.68/0.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.68/0.87  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['47', '48'])).
% 0.68/0.87  thf('71', plain,
% 0.68/0.87      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.68/0.87         = (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.68/0.87      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.68/0.87  thf(t94_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( k2_xboole_0 @ A @ B ) =
% 0.68/0.87       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.68/0.87  thf('72', plain,
% 0.68/0.87      (![X30 : $i, X31 : $i]:
% 0.68/0.87         ((k2_xboole_0 @ X30 @ X31)
% 0.68/0.87           = (k5_xboole_0 @ (k5_xboole_0 @ X30 @ X31) @ 
% 0.68/0.87              (k3_xboole_0 @ X30 @ X31)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.68/0.87  thf(l51_zfmisc_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.87  thf('73', plain,
% 0.68/0.87      (![X64 : $i, X65 : $i]:
% 0.68/0.87         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 0.68/0.87      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.68/0.87  thf('74', plain,
% 0.68/0.87      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.68/0.87         ((k5_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ X29)
% 0.68/0.87           = (k5_xboole_0 @ X27 @ (k5_xboole_0 @ X28 @ X29)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.68/0.87  thf('75', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ X0 @ X1)
% 0.68/0.87           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['10', '11'])).
% 0.68/0.87  thf('76', plain,
% 0.68/0.87      (![X30 : $i, X31 : $i]:
% 0.68/0.87         ((k3_tarski @ (k2_tarski @ X30 @ X31))
% 0.68/0.87           = (k5_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30)))),
% 0.68/0.87      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.68/0.87  thf('77', plain,
% 0.68/0.87      (((k3_tarski @ (k2_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.68/0.87         = (k5_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['71', '76'])).
% 0.68/0.87  thf('78', plain,
% 0.68/0.87      (((k3_tarski @ (k2_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.68/0.87         = (sk_A))),
% 0.68/0.87      inference('sup+', [status(thm)], ['51', '77'])).
% 0.68/0.87  thf('79', plain,
% 0.68/0.87      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.68/0.87         != (k2_subset_1 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.68/0.87  thf('80', plain, (![X69 : $i]: ((k2_subset_1 @ X69) = (X69))),
% 0.68/0.87      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.68/0.87  thf('81', plain,
% 0.68/0.87      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) != (sk_A))),
% 0.68/0.87      inference('demod', [status(thm)], ['79', '80'])).
% 0.68/0.87  thf('82', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(dt_k3_subset_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.87       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.68/0.87  thf('83', plain,
% 0.68/0.87      (![X72 : $i, X73 : $i]:
% 0.68/0.87         ((m1_subset_1 @ (k3_subset_1 @ X72 @ X73) @ (k1_zfmisc_1 @ X72))
% 0.68/0.87          | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ X72)))),
% 0.68/0.87      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.68/0.87  thf('84', plain,
% 0.68/0.87      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['82', '83'])).
% 0.68/0.87  thf('85', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(redefinition_k4_subset_1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.68/0.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.68/0.87       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.68/0.87  thf('86', plain,
% 0.68/0.87      (![X75 : $i, X76 : $i, X77 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X75 @ (k1_zfmisc_1 @ X76))
% 0.68/0.87          | ~ (m1_subset_1 @ X77 @ (k1_zfmisc_1 @ X76))
% 0.68/0.87          | ((k4_subset_1 @ X76 @ X75 @ X77) = (k2_xboole_0 @ X75 @ X77)))),
% 0.68/0.87      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.68/0.87  thf('87', plain,
% 0.68/0.87      (![X64 : $i, X65 : $i]:
% 0.68/0.87         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 0.68/0.87      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.68/0.87  thf('88', plain,
% 0.68/0.87      (![X75 : $i, X76 : $i, X77 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X75 @ (k1_zfmisc_1 @ X76))
% 0.68/0.87          | ~ (m1_subset_1 @ X77 @ (k1_zfmisc_1 @ X76))
% 0.68/0.87          | ((k4_subset_1 @ X76 @ X75 @ X77)
% 0.68/0.87              = (k3_tarski @ (k2_tarski @ X75 @ X77))))),
% 0.68/0.87      inference('demod', [status(thm)], ['86', '87'])).
% 0.68/0.87  thf('89', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         (((k4_subset_1 @ sk_A @ sk_B_1 @ X0)
% 0.68/0.87            = (k3_tarski @ (k2_tarski @ sk_B_1 @ X0)))
% 0.68/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['85', '88'])).
% 0.68/0.87  thf('90', plain,
% 0.68/0.87      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.68/0.87         = (k3_tarski @ (k2_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.68/0.87      inference('sup-', [status(thm)], ['84', '89'])).
% 0.68/0.87  thf('91', plain,
% 0.68/0.87      (((k3_tarski @ (k2_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.68/0.87         != (sk_A))),
% 0.68/0.87      inference('demod', [status(thm)], ['81', '90'])).
% 0.68/0.87  thf('92', plain, ($false),
% 0.68/0.87      inference('simplify_reflect-', [status(thm)], ['78', '91'])).
% 0.68/0.87  
% 0.68/0.87  % SZS output end Refutation
% 0.68/0.87  
% 0.68/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
