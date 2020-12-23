%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jOOPWOZvht

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:51 EST 2020

% Result     : Theorem 7.17s
% Output     : Refutation 7.17s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 140 expanded)
%              Number of leaves         :   28 (  53 expanded)
%              Depth                    :   18
%              Number of atoms          :  727 (1084 expanded)
%              Number of equality atoms :   54 (  68 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k4_subset_1 @ X36 @ X35 @ X37 )
        = ( k2_xboole_0 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('22',plain,(
    ! [X32: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('23',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( r1_tarski @ X23 @ X21 )
      | ( X22
       != ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('25',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_tarski @ X23 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ sk_A )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','30'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('33',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X32: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('42',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_tarski @ X23 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('44',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('46',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_A )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['37','48'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('51',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X22 )
      | ( X22
       != ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('62',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','63'])).

thf('65',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( m1_subset_1 @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X32: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('68',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['66','67'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('69',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('70',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('72',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('76',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['70','73','76'])).

thf('78',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['8','77','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jOOPWOZvht
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 7.17/7.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.17/7.40  % Solved by: fo/fo7.sh
% 7.17/7.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.17/7.40  % done 9279 iterations in 6.961s
% 7.17/7.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.17/7.40  % SZS output start Refutation
% 7.17/7.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.17/7.40  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 7.17/7.40  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.17/7.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.17/7.40  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 7.17/7.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.17/7.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.17/7.40  thf(sk_C_1_type, type, sk_C_1: $i).
% 7.17/7.40  thf(sk_B_type, type, sk_B: $i).
% 7.17/7.40  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.17/7.40  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.17/7.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.17/7.40  thf(sk_A_type, type, sk_A: $i).
% 7.17/7.40  thf(t41_subset_1, conjecture,
% 7.17/7.40    (![A:$i,B:$i]:
% 7.17/7.40     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.17/7.40       ( ![C:$i]:
% 7.17/7.40         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.17/7.40           ( r1_tarski @
% 7.17/7.40             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 7.17/7.40             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 7.17/7.40  thf(zf_stmt_0, negated_conjecture,
% 7.17/7.40    (~( ![A:$i,B:$i]:
% 7.17/7.40        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.17/7.40          ( ![C:$i]:
% 7.17/7.40            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.17/7.40              ( r1_tarski @
% 7.17/7.40                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 7.17/7.40                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 7.17/7.40    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 7.17/7.40  thf('0', plain,
% 7.17/7.40      (~ (r1_tarski @ 
% 7.17/7.40          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 7.17/7.40          (k3_subset_1 @ sk_A @ sk_B))),
% 7.17/7.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.17/7.40  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 7.17/7.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.17/7.40  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 7.17/7.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.17/7.41  thf(redefinition_k4_subset_1, axiom,
% 7.17/7.41    (![A:$i,B:$i,C:$i]:
% 7.17/7.41     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 7.17/7.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 7.17/7.41       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 7.17/7.41  thf('3', plain,
% 7.17/7.41      (![X35 : $i, X36 : $i, X37 : $i]:
% 7.17/7.41         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 7.17/7.41          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36))
% 7.17/7.41          | ((k4_subset_1 @ X36 @ X35 @ X37) = (k2_xboole_0 @ X35 @ X37)))),
% 7.17/7.41      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 7.17/7.41  thf('4', plain,
% 7.17/7.41      (![X0 : $i]:
% 7.17/7.41         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 7.17/7.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 7.17/7.41      inference('sup-', [status(thm)], ['2', '3'])).
% 7.17/7.41  thf('5', plain,
% 7.17/7.41      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 7.17/7.41      inference('sup-', [status(thm)], ['1', '4'])).
% 7.17/7.41  thf(commutativity_k2_xboole_0, axiom,
% 7.17/7.41    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 7.17/7.41  thf('6', plain,
% 7.17/7.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.17/7.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.17/7.41  thf('7', plain,
% 7.17/7.41      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_C_1 @ sk_B))),
% 7.17/7.41      inference('demod', [status(thm)], ['5', '6'])).
% 7.17/7.41  thf('8', plain,
% 7.17/7.41      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 7.17/7.41          (k3_subset_1 @ sk_A @ sk_B))),
% 7.17/7.41      inference('demod', [status(thm)], ['0', '7'])).
% 7.17/7.41  thf(t41_xboole_1, axiom,
% 7.17/7.41    (![A:$i,B:$i,C:$i]:
% 7.17/7.41     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 7.17/7.41       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 7.17/7.41  thf('9', plain,
% 7.17/7.41      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.17/7.41         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 7.17/7.41           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 7.17/7.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 7.17/7.41  thf(d10_xboole_0, axiom,
% 7.17/7.41    (![A:$i,B:$i]:
% 7.17/7.41     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.17/7.41  thf('10', plain,
% 7.17/7.41      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 7.17/7.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.17/7.41  thf('11', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 7.17/7.41      inference('simplify', [status(thm)], ['10'])).
% 7.17/7.41  thf(t12_xboole_1, axiom,
% 7.17/7.41    (![A:$i,B:$i]:
% 7.17/7.41     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 7.17/7.41  thf('12', plain,
% 7.17/7.41      (![X5 : $i, X6 : $i]:
% 7.17/7.41         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 7.17/7.41      inference('cnf', [status(esa)], [t12_xboole_1])).
% 7.17/7.41  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 7.17/7.41      inference('sup-', [status(thm)], ['11', '12'])).
% 7.17/7.41  thf('14', plain,
% 7.17/7.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.17/7.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.17/7.41  thf(t46_xboole_1, axiom,
% 7.17/7.41    (![A:$i,B:$i]:
% 7.17/7.41     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 7.17/7.41  thf('15', plain,
% 7.17/7.41      (![X18 : $i, X19 : $i]:
% 7.17/7.41         ((k4_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (k1_xboole_0))),
% 7.17/7.41      inference('cnf', [status(esa)], [t46_xboole_1])).
% 7.17/7.41  thf('16', plain,
% 7.17/7.41      (![X0 : $i, X1 : $i]:
% 7.17/7.41         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 7.17/7.41      inference('sup+', [status(thm)], ['14', '15'])).
% 7.17/7.41  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 7.17/7.41      inference('sup+', [status(thm)], ['13', '16'])).
% 7.17/7.41  thf('18', plain,
% 7.17/7.41      (![X0 : $i, X1 : $i]:
% 7.17/7.41         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 7.17/7.41           = (k1_xboole_0))),
% 7.17/7.41      inference('sup+', [status(thm)], ['9', '17'])).
% 7.17/7.41  thf('19', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 7.17/7.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.17/7.41  thf(d2_subset_1, axiom,
% 7.17/7.41    (![A:$i,B:$i]:
% 7.17/7.41     ( ( ( v1_xboole_0 @ A ) =>
% 7.17/7.41         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 7.17/7.41       ( ( ~( v1_xboole_0 @ A ) ) =>
% 7.17/7.41         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 7.17/7.41  thf('20', plain,
% 7.17/7.41      (![X25 : $i, X26 : $i]:
% 7.17/7.41         (~ (m1_subset_1 @ X25 @ X26)
% 7.17/7.41          | (r2_hidden @ X25 @ X26)
% 7.17/7.41          | (v1_xboole_0 @ X26))),
% 7.17/7.41      inference('cnf', [status(esa)], [d2_subset_1])).
% 7.17/7.41  thf('21', plain,
% 7.17/7.41      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 7.17/7.41        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 7.17/7.41      inference('sup-', [status(thm)], ['19', '20'])).
% 7.17/7.41  thf(fc1_subset_1, axiom,
% 7.17/7.41    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 7.17/7.41  thf('22', plain, (![X32 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 7.17/7.41      inference('cnf', [status(esa)], [fc1_subset_1])).
% 7.17/7.41  thf('23', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 7.17/7.41      inference('clc', [status(thm)], ['21', '22'])).
% 7.17/7.41  thf(d1_zfmisc_1, axiom,
% 7.17/7.41    (![A:$i,B:$i]:
% 7.17/7.41     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 7.17/7.41       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 7.17/7.41  thf('24', plain,
% 7.17/7.41      (![X21 : $i, X22 : $i, X23 : $i]:
% 7.17/7.41         (~ (r2_hidden @ X23 @ X22)
% 7.17/7.41          | (r1_tarski @ X23 @ X21)
% 7.17/7.41          | ((X22) != (k1_zfmisc_1 @ X21)))),
% 7.17/7.41      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 7.17/7.41  thf('25', plain,
% 7.17/7.41      (![X21 : $i, X23 : $i]:
% 7.17/7.41         ((r1_tarski @ X23 @ X21) | ~ (r2_hidden @ X23 @ (k1_zfmisc_1 @ X21)))),
% 7.17/7.41      inference('simplify', [status(thm)], ['24'])).
% 7.17/7.41  thf('26', plain, ((r1_tarski @ sk_B @ sk_A)),
% 7.17/7.41      inference('sup-', [status(thm)], ['23', '25'])).
% 7.17/7.41  thf('27', plain,
% 7.17/7.41      (![X5 : $i, X6 : $i]:
% 7.17/7.41         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 7.17/7.41      inference('cnf', [status(esa)], [t12_xboole_1])).
% 7.17/7.41  thf('28', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 7.17/7.41      inference('sup-', [status(thm)], ['26', '27'])).
% 7.17/7.41  thf('29', plain,
% 7.17/7.41      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.17/7.41         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 7.17/7.41           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 7.17/7.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 7.17/7.41  thf('30', plain,
% 7.17/7.41      (![X0 : $i]:
% 7.17/7.41         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)
% 7.17/7.41           = (k4_xboole_0 @ X0 @ sk_A))),
% 7.17/7.41      inference('sup+', [status(thm)], ['28', '29'])).
% 7.17/7.41  thf('31', plain,
% 7.17/7.41      (![X0 : $i]:
% 7.17/7.41         ((k4_xboole_0 @ k1_xboole_0 @ sk_A)
% 7.17/7.41           = (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ 
% 7.17/7.41              sk_A))),
% 7.17/7.41      inference('sup+', [status(thm)], ['18', '30'])).
% 7.17/7.41  thf(t36_xboole_1, axiom,
% 7.17/7.41    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 7.17/7.41  thf('32', plain,
% 7.17/7.41      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 7.17/7.41      inference('cnf', [status(esa)], [t36_xboole_1])).
% 7.17/7.41  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 7.17/7.41  thf('33', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 7.17/7.41      inference('cnf', [status(esa)], [t2_xboole_1])).
% 7.17/7.41  thf('34', plain,
% 7.17/7.41      (![X2 : $i, X4 : $i]:
% 7.17/7.41         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 7.17/7.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.17/7.41  thf('35', plain,
% 7.17/7.41      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 7.17/7.41      inference('sup-', [status(thm)], ['33', '34'])).
% 7.17/7.41  thf('36', plain,
% 7.17/7.41      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 7.17/7.41      inference('sup-', [status(thm)], ['32', '35'])).
% 7.17/7.41  thf('37', plain,
% 7.17/7.41      (![X0 : $i]:
% 7.17/7.41         ((k1_xboole_0)
% 7.17/7.41           = (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ 
% 7.17/7.41              sk_A))),
% 7.17/7.41      inference('demod', [status(thm)], ['31', '36'])).
% 7.17/7.41  thf('38', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 7.17/7.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.17/7.41  thf('39', plain,
% 7.17/7.41      (![X25 : $i, X26 : $i]:
% 7.17/7.41         (~ (m1_subset_1 @ X25 @ X26)
% 7.17/7.41          | (r2_hidden @ X25 @ X26)
% 7.17/7.41          | (v1_xboole_0 @ X26))),
% 7.17/7.41      inference('cnf', [status(esa)], [d2_subset_1])).
% 7.17/7.41  thf('40', plain,
% 7.17/7.41      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 7.17/7.41        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 7.17/7.41      inference('sup-', [status(thm)], ['38', '39'])).
% 7.17/7.41  thf('41', plain, (![X32 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 7.17/7.41      inference('cnf', [status(esa)], [fc1_subset_1])).
% 7.17/7.41  thf('42', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 7.17/7.41      inference('clc', [status(thm)], ['40', '41'])).
% 7.17/7.41  thf('43', plain,
% 7.17/7.41      (![X21 : $i, X23 : $i]:
% 7.17/7.41         ((r1_tarski @ X23 @ X21) | ~ (r2_hidden @ X23 @ (k1_zfmisc_1 @ X21)))),
% 7.17/7.41      inference('simplify', [status(thm)], ['24'])).
% 7.17/7.41  thf('44', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 7.17/7.41      inference('sup-', [status(thm)], ['42', '43'])).
% 7.17/7.41  thf('45', plain,
% 7.17/7.41      (![X5 : $i, X6 : $i]:
% 7.17/7.41         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 7.17/7.41      inference('cnf', [status(esa)], [t12_xboole_1])).
% 7.17/7.41  thf('46', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 7.17/7.41      inference('sup-', [status(thm)], ['44', '45'])).
% 7.17/7.41  thf('47', plain,
% 7.17/7.41      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.17/7.41         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 7.17/7.41           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 7.17/7.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 7.17/7.41  thf('48', plain,
% 7.17/7.41      (![X0 : $i]:
% 7.17/7.41         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_A)
% 7.17/7.41           = (k4_xboole_0 @ X0 @ sk_A))),
% 7.17/7.41      inference('sup+', [status(thm)], ['46', '47'])).
% 7.17/7.41  thf('49', plain,
% 7.17/7.41      (((k1_xboole_0) = (k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A))),
% 7.17/7.41      inference('sup+', [status(thm)], ['37', '48'])).
% 7.17/7.41  thf(t39_xboole_1, axiom,
% 7.17/7.41    (![A:$i,B:$i]:
% 7.17/7.41     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 7.17/7.41  thf('50', plain,
% 7.17/7.41      (![X10 : $i, X11 : $i]:
% 7.17/7.41         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 7.17/7.41           = (k2_xboole_0 @ X10 @ X11))),
% 7.17/7.41      inference('cnf', [status(esa)], [t39_xboole_1])).
% 7.17/7.41  thf('51', plain,
% 7.17/7.41      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 7.17/7.41         = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 7.17/7.41      inference('sup+', [status(thm)], ['49', '50'])).
% 7.17/7.41  thf('52', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 7.17/7.41      inference('cnf', [status(esa)], [t2_xboole_1])).
% 7.17/7.41  thf('53', plain,
% 7.17/7.41      (![X5 : $i, X6 : $i]:
% 7.17/7.41         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 7.17/7.41      inference('cnf', [status(esa)], [t12_xboole_1])).
% 7.17/7.41  thf('54', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 7.17/7.41      inference('sup-', [status(thm)], ['52', '53'])).
% 7.17/7.41  thf('55', plain,
% 7.17/7.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.17/7.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.17/7.41  thf('56', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 7.17/7.41      inference('sup+', [status(thm)], ['54', '55'])).
% 7.17/7.41  thf('57', plain,
% 7.17/7.41      (((sk_A) = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 7.17/7.41      inference('demod', [status(thm)], ['51', '56'])).
% 7.17/7.41  thf('58', plain,
% 7.17/7.41      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 7.17/7.41      inference('cnf', [status(esa)], [t36_xboole_1])).
% 7.17/7.41  thf(t44_xboole_1, axiom,
% 7.17/7.41    (![A:$i,B:$i,C:$i]:
% 7.17/7.41     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 7.17/7.41       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 7.17/7.41  thf('59', plain,
% 7.17/7.41      (![X15 : $i, X16 : $i, X17 : $i]:
% 7.17/7.41         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 7.17/7.41          | ~ (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17))),
% 7.17/7.41      inference('cnf', [status(esa)], [t44_xboole_1])).
% 7.17/7.41  thf('60', plain,
% 7.17/7.41      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 7.17/7.41      inference('sup-', [status(thm)], ['58', '59'])).
% 7.17/7.41  thf('61', plain,
% 7.17/7.41      (![X20 : $i, X21 : $i, X22 : $i]:
% 7.17/7.41         (~ (r1_tarski @ X20 @ X21)
% 7.17/7.41          | (r2_hidden @ X20 @ X22)
% 7.17/7.41          | ((X22) != (k1_zfmisc_1 @ X21)))),
% 7.17/7.41      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 7.17/7.41  thf('62', plain,
% 7.17/7.41      (![X20 : $i, X21 : $i]:
% 7.17/7.41         ((r2_hidden @ X20 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X20 @ X21))),
% 7.17/7.41      inference('simplify', [status(thm)], ['61'])).
% 7.17/7.41  thf('63', plain,
% 7.17/7.41      (![X0 : $i, X1 : $i]:
% 7.17/7.41         (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 7.17/7.41      inference('sup-', [status(thm)], ['60', '62'])).
% 7.17/7.41  thf('64', plain,
% 7.17/7.41      ((r2_hidden @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 7.17/7.41      inference('sup+', [status(thm)], ['57', '63'])).
% 7.17/7.41  thf('65', plain,
% 7.17/7.41      (![X25 : $i, X26 : $i]:
% 7.17/7.41         (~ (r2_hidden @ X25 @ X26)
% 7.17/7.41          | (m1_subset_1 @ X25 @ X26)
% 7.17/7.41          | (v1_xboole_0 @ X26))),
% 7.17/7.41      inference('cnf', [status(esa)], [d2_subset_1])).
% 7.17/7.41  thf('66', plain,
% 7.17/7.41      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 7.17/7.41        | (m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 7.17/7.41      inference('sup-', [status(thm)], ['64', '65'])).
% 7.17/7.41  thf('67', plain, (![X32 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 7.17/7.41      inference('cnf', [status(esa)], [fc1_subset_1])).
% 7.17/7.41  thf('68', plain,
% 7.17/7.41      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 7.17/7.41      inference('clc', [status(thm)], ['66', '67'])).
% 7.17/7.41  thf(d5_subset_1, axiom,
% 7.17/7.41    (![A:$i,B:$i]:
% 7.17/7.41     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.17/7.41       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 7.17/7.41  thf('69', plain,
% 7.17/7.41      (![X28 : $i, X29 : $i]:
% 7.17/7.41         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 7.17/7.41          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 7.17/7.41      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.17/7.41  thf('70', plain,
% 7.17/7.41      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 7.17/7.41         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 7.17/7.41      inference('sup-', [status(thm)], ['68', '69'])).
% 7.17/7.41  thf('71', plain,
% 7.17/7.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.17/7.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.17/7.41  thf('72', plain,
% 7.17/7.41      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.17/7.41         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 7.17/7.41           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 7.17/7.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 7.17/7.41  thf('73', plain,
% 7.17/7.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.17/7.41         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 7.17/7.41           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 7.17/7.41      inference('sup+', [status(thm)], ['71', '72'])).
% 7.17/7.41  thf('74', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 7.17/7.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.17/7.41  thf('75', plain,
% 7.17/7.41      (![X28 : $i, X29 : $i]:
% 7.17/7.41         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 7.17/7.41          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 7.17/7.41      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.17/7.41  thf('76', plain,
% 7.17/7.41      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 7.17/7.41      inference('sup-', [status(thm)], ['74', '75'])).
% 7.17/7.41  thf('77', plain,
% 7.17/7.41      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 7.17/7.41         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 7.17/7.41      inference('demod', [status(thm)], ['70', '73', '76'])).
% 7.17/7.41  thf('78', plain,
% 7.17/7.41      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 7.17/7.41      inference('cnf', [status(esa)], [t36_xboole_1])).
% 7.17/7.41  thf('79', plain, ($false),
% 7.17/7.41      inference('demod', [status(thm)], ['8', '77', '78'])).
% 7.17/7.41  
% 7.17/7.41  % SZS output end Refutation
% 7.17/7.41  
% 7.17/7.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
