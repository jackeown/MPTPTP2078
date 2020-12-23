%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jOb9zADqj2

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:18 EST 2020

% Result     : Theorem 7.22s
% Output     : Refutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 907 expanded)
%              Number of leaves         :   37 ( 295 expanded)
%              Depth                    :   17
%              Number of atoms          : 1447 (7348 expanded)
%              Number of equality atoms :  105 ( 423 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t35_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
             => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k3_subset_1 @ X45 @ X46 )
        = ( k4_xboole_0 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ X43 )
      | ( r2_hidden @ X42 @ X43 )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X47: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('9',plain,(
    r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(t92_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ ( k3_tarski @ X40 ) )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t92_zfmisc_1])).

thf('11',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('12',plain,(
    ! [X41: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('13',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t104_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ~ ( r2_xboole_0 @ A @ B )
          & ( A != B )
          & ~ ( r2_xboole_0 @ B @ A ) )
    <=> ( r3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r3_xboole_0 @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[t104_xboole_1])).

thf('17',plain,(
    ! [X10: $i] :
      ( r3_xboole_0 @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        | ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X5 @ X4 )
      | ~ ( r3_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t107_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k5_xboole_0 @ X34 @ ( k5_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X37 @ X38 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X37 @ X38 ) @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('35',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k5_xboole_0 @ X34 @ ( k5_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('36',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X37 @ X38 )
      = ( k5_xboole_0 @ X37 @ ( k5_xboole_0 @ X38 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33','36'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X37 @ X38 )
      = ( k5_xboole_0 @ X37 @ ( k5_xboole_0 @ X38 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('42',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k5_xboole_0 @ X34 @ ( k5_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('43',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ X0 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('52',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ X0 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','54'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k2_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ X43 )
      | ( r2_hidden @ X42 @ X43 )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X47: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('63',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ ( k3_tarski @ X40 ) )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t92_zfmisc_1])).

thf('65',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X41: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('67',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('69',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k2_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ X0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = sk_B ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( r1_tarski @ X12 @ ( k5_xboole_0 @ X13 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X15 ) )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ sk_B )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ X0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ sk_B )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ( r1_tarski @ X1 @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_A ) ) )
    | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['58','77'])).

thf('79',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t14_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf('81',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ( r1_tarski @ X18 @ ( sk_D @ X20 @ X19 @ X18 ) )
      | ( X19
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ X0 @ ( sk_D @ X1 @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( r1_tarski @ sk_A @ ( sk_D @ sk_C @ sk_A @ sk_A ) )
    | ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( r1_tarski @ X19 @ ( sk_D @ X20 @ X19 @ X18 ) )
      | ( X19
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('85',plain,
    ( ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_C ) )
    | ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('88',plain,
    ( ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_C ) )
    | ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X37 @ X38 )
      = ( k5_xboole_0 @ X37 @ ( k5_xboole_0 @ X38 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('91',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('94',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('96',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k5_xboole_0 @ X34 @ ( k5_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('102',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','100','101'])).

thf('103',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('104',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X37 @ X38 )
      = ( k5_xboole_0 @ X37 @ ( k5_xboole_0 @ X38 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('105',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('107',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('108',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('110',plain,
    ( sk_C
    = ( k5_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','108','109'])).

thf('111',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['102','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('113',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['65','66'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ X0 @ ( sk_D @ X1 @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('117',plain,
    ( ( r1_tarski @ sk_A @ ( sk_D @ sk_B @ sk_A @ sk_A ) )
    | ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( r1_tarski @ X19 @ ( sk_D @ X20 @ X19 @ X18 ) )
      | ( X19
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('119',plain,
    ( ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['65','66'])).

thf('121',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('122',plain,
    ( ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X37 @ X38 )
      = ( k5_xboole_0 @ X37 @ ( k5_xboole_0 @ X38 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('125',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','99'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('128',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['67','68'])).

thf('130',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X37 @ X38 )
      = ( k5_xboole_0 @ X37 @ ( k5_xboole_0 @ X38 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('131',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['65','66'])).

thf('133',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('134',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('136',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','134','135'])).

thf('137',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['128','136'])).

thf('138',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('139',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('141',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['102','110'])).

thf('143',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k3_subset_1 @ X45 @ X46 )
        = ( k4_xboole_0 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('146',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['143','146'])).

thf('148',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('149',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['147','150'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('152',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('153',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ sk_B ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['102','110'])).

thf('155',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['102','110'])).

thf('156',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['78','111','114','141','142','156'])).

thf('158',plain,(
    $false ),
    inference(demod,[status(thm)],['4','157'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jOb9zADqj2
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:05:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 7.22/7.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.22/7.42  % Solved by: fo/fo7.sh
% 7.22/7.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.22/7.42  % done 6848 iterations in 6.953s
% 7.22/7.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.22/7.42  % SZS output start Refutation
% 7.22/7.42  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 7.22/7.42  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.22/7.42  thf(sk_C_type, type, sk_C: $i).
% 7.22/7.42  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.22/7.42  thf(sk_A_type, type, sk_A: $i).
% 7.22/7.42  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.22/7.42  thf(sk_B_type, type, sk_B: $i).
% 7.22/7.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.22/7.42  thf(r3_xboole_0_type, type, r3_xboole_0: $i > $i > $o).
% 7.22/7.42  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 7.22/7.42  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 7.22/7.42  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 7.22/7.42  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 7.22/7.42  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.22/7.42  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 7.22/7.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.22/7.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.22/7.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.22/7.42  thf(t35_subset_1, conjecture,
% 7.22/7.42    (![A:$i,B:$i]:
% 7.22/7.42     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.22/7.42       ( ![C:$i]:
% 7.22/7.42         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.22/7.42           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 7.22/7.42             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 7.22/7.42  thf(zf_stmt_0, negated_conjecture,
% 7.22/7.42    (~( ![A:$i,B:$i]:
% 7.22/7.42        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.22/7.42          ( ![C:$i]:
% 7.22/7.42            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.22/7.42              ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 7.22/7.42                ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 7.22/7.42    inference('cnf.neg', [status(esa)], [t35_subset_1])).
% 7.22/7.42  thf('0', plain, (~ (r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ sk_B))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf(d5_subset_1, axiom,
% 7.22/7.42    (![A:$i,B:$i]:
% 7.22/7.42     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.22/7.42       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 7.22/7.42  thf('2', plain,
% 7.22/7.42      (![X45 : $i, X46 : $i]:
% 7.22/7.42         (((k3_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))
% 7.22/7.42          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45)))),
% 7.22/7.42      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.22/7.42  thf('3', plain,
% 7.22/7.42      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 7.22/7.42      inference('sup-', [status(thm)], ['1', '2'])).
% 7.22/7.42  thf('4', plain, (~ (r1_tarski @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))),
% 7.22/7.42      inference('demod', [status(thm)], ['0', '3'])).
% 7.22/7.42  thf('5', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf(d2_subset_1, axiom,
% 7.22/7.42    (![A:$i,B:$i]:
% 7.22/7.42     ( ( ( v1_xboole_0 @ A ) =>
% 7.22/7.42         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 7.22/7.42       ( ( ~( v1_xboole_0 @ A ) ) =>
% 7.22/7.42         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 7.22/7.42  thf('6', plain,
% 7.22/7.42      (![X42 : $i, X43 : $i]:
% 7.22/7.42         (~ (m1_subset_1 @ X42 @ X43)
% 7.22/7.42          | (r2_hidden @ X42 @ X43)
% 7.22/7.42          | (v1_xboole_0 @ X43))),
% 7.22/7.42      inference('cnf', [status(esa)], [d2_subset_1])).
% 7.22/7.42  thf('7', plain,
% 7.22/7.42      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 7.22/7.42        | (r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 7.22/7.42      inference('sup-', [status(thm)], ['5', '6'])).
% 7.22/7.42  thf(fc1_subset_1, axiom,
% 7.22/7.42    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 7.22/7.42  thf('8', plain, (![X47 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X47))),
% 7.22/7.42      inference('cnf', [status(esa)], [fc1_subset_1])).
% 7.22/7.42  thf('9', plain, ((r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 7.22/7.42      inference('clc', [status(thm)], ['7', '8'])).
% 7.22/7.42  thf(t92_zfmisc_1, axiom,
% 7.22/7.42    (![A:$i,B:$i]:
% 7.22/7.42     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 7.22/7.42  thf('10', plain,
% 7.22/7.42      (![X39 : $i, X40 : $i]:
% 7.22/7.42         ((r1_tarski @ X39 @ (k3_tarski @ X40)) | ~ (r2_hidden @ X39 @ X40))),
% 7.22/7.42      inference('cnf', [status(esa)], [t92_zfmisc_1])).
% 7.22/7.42  thf('11', plain, ((r1_tarski @ sk_C @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 7.22/7.42      inference('sup-', [status(thm)], ['9', '10'])).
% 7.22/7.42  thf(t99_zfmisc_1, axiom,
% 7.22/7.42    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 7.22/7.42  thf('12', plain, (![X41 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X41)) = (X41))),
% 7.22/7.42      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 7.22/7.42  thf('13', plain, ((r1_tarski @ sk_C @ sk_A)),
% 7.22/7.42      inference('demod', [status(thm)], ['11', '12'])).
% 7.22/7.42  thf(t12_xboole_1, axiom,
% 7.22/7.42    (![A:$i,B:$i]:
% 7.22/7.42     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 7.22/7.42  thf('14', plain,
% 7.22/7.42      (![X16 : $i, X17 : $i]:
% 7.22/7.42         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 7.22/7.42      inference('cnf', [status(esa)], [t12_xboole_1])).
% 7.22/7.42  thf('15', plain, (((k2_xboole_0 @ sk_C @ sk_A) = (sk_A))),
% 7.22/7.42      inference('sup-', [status(thm)], ['13', '14'])).
% 7.22/7.42  thf(t104_xboole_1, axiom,
% 7.22/7.42    (![A:$i,B:$i]:
% 7.22/7.42     ( ( ~( ( ~( r2_xboole_0 @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 7.22/7.42            ( ~( r2_xboole_0 @ B @ A ) ) ) ) <=>
% 7.22/7.42       ( r3_xboole_0 @ A @ B ) ))).
% 7.22/7.42  thf('16', plain,
% 7.22/7.42      (![X9 : $i, X10 : $i]: ((r3_xboole_0 @ X9 @ X10) | ((X9) != (X10)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t104_xboole_1])).
% 7.22/7.42  thf('17', plain, (![X10 : $i]: (r3_xboole_0 @ X10 @ X10)),
% 7.22/7.42      inference('simplify', [status(thm)], ['16'])).
% 7.22/7.42  thf(d9_xboole_0, axiom,
% 7.22/7.42    (![A:$i,B:$i]:
% 7.22/7.42     ( ( r3_xboole_0 @ A @ B ) <=>
% 7.22/7.42       ( ( r1_tarski @ A @ B ) | ( r1_tarski @ B @ A ) ) ))).
% 7.22/7.42  thf('18', plain,
% 7.22/7.42      (![X4 : $i, X5 : $i]:
% 7.22/7.42         ((r1_tarski @ X4 @ X5)
% 7.22/7.42          | (r1_tarski @ X5 @ X4)
% 7.22/7.42          | ~ (r3_xboole_0 @ X5 @ X4))),
% 7.22/7.42      inference('cnf', [status(esa)], [d9_xboole_0])).
% 7.22/7.42  thf('19', plain,
% 7.22/7.42      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 7.22/7.42      inference('sup-', [status(thm)], ['17', '18'])).
% 7.22/7.42  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 7.22/7.42      inference('simplify', [status(thm)], ['19'])).
% 7.22/7.42  thf(commutativity_k5_xboole_0, axiom,
% 7.22/7.42    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 7.22/7.42  thf('21', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 7.22/7.42      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 7.22/7.42  thf(t107_xboole_1, axiom,
% 7.22/7.42    (![A:$i,B:$i,C:$i]:
% 7.22/7.42     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 7.22/7.42       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 7.22/7.42         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 7.22/7.42  thf('22', plain,
% 7.22/7.42      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.22/7.42         ((r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14))
% 7.22/7.42          | ~ (r1_tarski @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t107_xboole_1])).
% 7.22/7.42  thf('23', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.22/7.42         (~ (r1_tarski @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 7.22/7.42          | (r1_tarski @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 7.22/7.42      inference('sup-', [status(thm)], ['21', '22'])).
% 7.22/7.42  thf('24', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         (r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))),
% 7.22/7.42      inference('sup-', [status(thm)], ['20', '23'])).
% 7.22/7.42  thf('25', plain,
% 7.22/7.42      (![X16 : $i, X17 : $i]:
% 7.22/7.42         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 7.22/7.42      inference('cnf', [status(esa)], [t12_xboole_1])).
% 7.22/7.42  thf('26', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 7.22/7.42           = (k2_xboole_0 @ X1 @ X0))),
% 7.22/7.42      inference('sup-', [status(thm)], ['24', '25'])).
% 7.22/7.42  thf('27', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 7.22/7.42      inference('simplify', [status(thm)], ['19'])).
% 7.22/7.42  thf('28', plain,
% 7.22/7.42      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.22/7.42         ((r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14))
% 7.22/7.42          | ~ (r1_tarski @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t107_xboole_1])).
% 7.22/7.42  thf('29', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         (r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 7.22/7.42      inference('sup-', [status(thm)], ['27', '28'])).
% 7.22/7.42  thf('30', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         (r1_tarski @ 
% 7.22/7.42          (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)) @ 
% 7.22/7.42          (k2_xboole_0 @ X1 @ X0))),
% 7.22/7.42      inference('sup+', [status(thm)], ['26', '29'])).
% 7.22/7.42  thf('31', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 7.22/7.42      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 7.22/7.42  thf(t91_xboole_1, axiom,
% 7.22/7.42    (![A:$i,B:$i,C:$i]:
% 7.22/7.42     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 7.22/7.42       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 7.22/7.42  thf('32', plain,
% 7.22/7.42      (![X34 : $i, X35 : $i, X36 : $i]:
% 7.22/7.42         ((k5_xboole_0 @ (k5_xboole_0 @ X34 @ X35) @ X36)
% 7.22/7.42           = (k5_xboole_0 @ X34 @ (k5_xboole_0 @ X35 @ X36)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t91_xboole_1])).
% 7.22/7.42  thf('33', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.22/7.42         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 7.22/7.42           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 7.22/7.42      inference('sup+', [status(thm)], ['31', '32'])).
% 7.22/7.42  thf(t95_xboole_1, axiom,
% 7.22/7.42    (![A:$i,B:$i]:
% 7.22/7.42     ( ( k3_xboole_0 @ A @ B ) =
% 7.22/7.42       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 7.22/7.42  thf('34', plain,
% 7.22/7.42      (![X37 : $i, X38 : $i]:
% 7.22/7.42         ((k3_xboole_0 @ X37 @ X38)
% 7.22/7.42           = (k5_xboole_0 @ (k5_xboole_0 @ X37 @ X38) @ 
% 7.22/7.42              (k2_xboole_0 @ X37 @ X38)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t95_xboole_1])).
% 7.22/7.42  thf('35', plain,
% 7.22/7.42      (![X34 : $i, X35 : $i, X36 : $i]:
% 7.22/7.42         ((k5_xboole_0 @ (k5_xboole_0 @ X34 @ X35) @ X36)
% 7.22/7.42           = (k5_xboole_0 @ X34 @ (k5_xboole_0 @ X35 @ X36)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t91_xboole_1])).
% 7.22/7.42  thf('36', plain,
% 7.22/7.42      (![X37 : $i, X38 : $i]:
% 7.22/7.42         ((k3_xboole_0 @ X37 @ X38)
% 7.22/7.42           = (k5_xboole_0 @ X37 @ 
% 7.22/7.42              (k5_xboole_0 @ X38 @ (k2_xboole_0 @ X37 @ X38))))),
% 7.22/7.42      inference('demod', [status(thm)], ['34', '35'])).
% 7.22/7.42  thf('37', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 7.22/7.42      inference('demod', [status(thm)], ['30', '33', '36'])).
% 7.22/7.42  thf(t7_xboole_1, axiom,
% 7.22/7.42    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 7.22/7.42  thf('38', plain,
% 7.22/7.42      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 7.22/7.42      inference('cnf', [status(esa)], [t7_xboole_1])).
% 7.22/7.42  thf(t28_xboole_1, axiom,
% 7.22/7.42    (![A:$i,B:$i]:
% 7.22/7.42     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 7.22/7.42  thf('39', plain,
% 7.22/7.42      (![X21 : $i, X22 : $i]:
% 7.22/7.42         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 7.22/7.42      inference('cnf', [status(esa)], [t28_xboole_1])).
% 7.22/7.42  thf('40', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 7.22/7.42      inference('sup-', [status(thm)], ['38', '39'])).
% 7.22/7.42  thf('41', plain,
% 7.22/7.42      (![X37 : $i, X38 : $i]:
% 7.22/7.42         ((k3_xboole_0 @ X37 @ X38)
% 7.22/7.42           = (k5_xboole_0 @ X37 @ 
% 7.22/7.42              (k5_xboole_0 @ X38 @ (k2_xboole_0 @ X37 @ X38))))),
% 7.22/7.42      inference('demod', [status(thm)], ['34', '35'])).
% 7.22/7.42  thf('42', plain,
% 7.22/7.42      (![X34 : $i, X35 : $i, X36 : $i]:
% 7.22/7.42         ((k5_xboole_0 @ (k5_xboole_0 @ X34 @ X35) @ X36)
% 7.22/7.42           = (k5_xboole_0 @ X34 @ (k5_xboole_0 @ X35 @ X36)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t91_xboole_1])).
% 7.22/7.42  thf('43', plain,
% 7.22/7.42      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.22/7.42         ((r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14))
% 7.22/7.42          | ~ (r1_tarski @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t107_xboole_1])).
% 7.22/7.42  thf('44', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.22/7.42         (~ (r1_tarski @ X3 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))
% 7.22/7.42          | (r1_tarski @ X3 @ (k2_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0)))),
% 7.22/7.42      inference('sup-', [status(thm)], ['42', '43'])).
% 7.22/7.42  thf('45', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.22/7.42         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 7.22/7.42          | (r1_tarski @ X2 @ 
% 7.22/7.42             (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 7.22/7.42      inference('sup-', [status(thm)], ['41', '44'])).
% 7.22/7.42  thf('46', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         (r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 7.22/7.42      inference('sup-', [status(thm)], ['27', '28'])).
% 7.22/7.42  thf('47', plain,
% 7.22/7.42      (![X16 : $i, X17 : $i]:
% 7.22/7.42         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 7.22/7.42      inference('cnf', [status(esa)], [t12_xboole_1])).
% 7.22/7.42  thf('48', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 7.22/7.42           = (k2_xboole_0 @ X1 @ X0))),
% 7.22/7.42      inference('sup-', [status(thm)], ['46', '47'])).
% 7.22/7.42  thf('49', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.22/7.42         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 7.22/7.42          | (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 7.22/7.42      inference('demod', [status(thm)], ['45', '48'])).
% 7.22/7.42  thf('50', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.22/7.42         (~ (r1_tarski @ X2 @ X0)
% 7.22/7.42          | (r1_tarski @ X2 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 7.22/7.42      inference('sup-', [status(thm)], ['40', '49'])).
% 7.22/7.42  thf('51', plain,
% 7.22/7.42      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 7.22/7.42      inference('cnf', [status(esa)], [t7_xboole_1])).
% 7.22/7.42  thf('52', plain,
% 7.22/7.42      (![X16 : $i, X17 : $i]:
% 7.22/7.42         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 7.22/7.42      inference('cnf', [status(esa)], [t12_xboole_1])).
% 7.22/7.42  thf('53', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 7.22/7.42           = (k2_xboole_0 @ X1 @ X0))),
% 7.22/7.42      inference('sup-', [status(thm)], ['51', '52'])).
% 7.22/7.42  thf('54', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.22/7.42         (~ (r1_tarski @ X2 @ X0) | (r1_tarski @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 7.22/7.42      inference('demod', [status(thm)], ['50', '53'])).
% 7.22/7.42  thf('55', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.22/7.42         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ 
% 7.22/7.42          (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 7.22/7.42      inference('sup-', [status(thm)], ['37', '54'])).
% 7.22/7.42  thf(t4_xboole_1, axiom,
% 7.22/7.42    (![A:$i,B:$i,C:$i]:
% 7.22/7.42     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 7.22/7.42       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 7.22/7.42  thf('56', plain,
% 7.22/7.42      (![X23 : $i, X24 : $i, X25 : $i]:
% 7.22/7.42         ((k2_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X25)
% 7.22/7.42           = (k2_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t4_xboole_1])).
% 7.22/7.42  thf('57', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.22/7.42         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ 
% 7.22/7.42          (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 7.22/7.42      inference('demod', [status(thm)], ['55', '56'])).
% 7.22/7.42  thf('58', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_A))),
% 7.22/7.42      inference('sup+', [status(thm)], ['15', '57'])).
% 7.22/7.42  thf('59', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf('60', plain,
% 7.22/7.42      (![X42 : $i, X43 : $i]:
% 7.22/7.42         (~ (m1_subset_1 @ X42 @ X43)
% 7.22/7.42          | (r2_hidden @ X42 @ X43)
% 7.22/7.42          | (v1_xboole_0 @ X43))),
% 7.22/7.42      inference('cnf', [status(esa)], [d2_subset_1])).
% 7.22/7.42  thf('61', plain,
% 7.22/7.42      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 7.22/7.42        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 7.22/7.42      inference('sup-', [status(thm)], ['59', '60'])).
% 7.22/7.42  thf('62', plain, (![X47 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X47))),
% 7.22/7.42      inference('cnf', [status(esa)], [fc1_subset_1])).
% 7.22/7.42  thf('63', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 7.22/7.42      inference('clc', [status(thm)], ['61', '62'])).
% 7.22/7.42  thf('64', plain,
% 7.22/7.42      (![X39 : $i, X40 : $i]:
% 7.22/7.42         ((r1_tarski @ X39 @ (k3_tarski @ X40)) | ~ (r2_hidden @ X39 @ X40))),
% 7.22/7.42      inference('cnf', [status(esa)], [t92_zfmisc_1])).
% 7.22/7.42  thf('65', plain, ((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 7.22/7.42      inference('sup-', [status(thm)], ['63', '64'])).
% 7.22/7.42  thf('66', plain, (![X41 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X41)) = (X41))),
% 7.22/7.42      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 7.22/7.42  thf('67', plain, ((r1_tarski @ sk_B @ sk_A)),
% 7.22/7.42      inference('demod', [status(thm)], ['65', '66'])).
% 7.22/7.42  thf('68', plain,
% 7.22/7.42      (![X16 : $i, X17 : $i]:
% 7.22/7.42         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 7.22/7.42      inference('cnf', [status(esa)], [t12_xboole_1])).
% 7.22/7.42  thf('69', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 7.22/7.42      inference('sup-', [status(thm)], ['67', '68'])).
% 7.22/7.42  thf('70', plain,
% 7.22/7.42      (![X23 : $i, X24 : $i, X25 : $i]:
% 7.22/7.42         ((k2_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X25)
% 7.22/7.42           = (k2_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t4_xboole_1])).
% 7.22/7.42  thf('71', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         ((k2_xboole_0 @ sk_A @ X0)
% 7.22/7.42           = (k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 7.22/7.42      inference('sup+', [status(thm)], ['69', '70'])).
% 7.22/7.42  thf('72', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 7.22/7.42      inference('sup-', [status(thm)], ['38', '39'])).
% 7.22/7.42  thf('73', plain,
% 7.22/7.42      (![X0 : $i]: ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)) = (sk_B))),
% 7.22/7.42      inference('sup+', [status(thm)], ['71', '72'])).
% 7.22/7.42  thf('74', plain,
% 7.22/7.42      (![X12 : $i, X13 : $i, X15 : $i]:
% 7.22/7.42         ((r1_tarski @ X12 @ (k5_xboole_0 @ X13 @ X15))
% 7.22/7.42          | ~ (r1_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X15))
% 7.22/7.42          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X15)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t107_xboole_1])).
% 7.22/7.42  thf('75', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         (~ (r1_xboole_0 @ X1 @ sk_B)
% 7.22/7.42          | ~ (r1_tarski @ X1 @ 
% 7.22/7.42               (k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))
% 7.22/7.42          | (r1_tarski @ X1 @ (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))))),
% 7.22/7.42      inference('sup-', [status(thm)], ['73', '74'])).
% 7.22/7.42  thf('76', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         ((k2_xboole_0 @ sk_A @ X0)
% 7.22/7.42           = (k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 7.22/7.42      inference('sup+', [status(thm)], ['69', '70'])).
% 7.22/7.42  thf('77', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         (~ (r1_xboole_0 @ X1 @ sk_B)
% 7.22/7.42          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_A @ X0))
% 7.22/7.42          | (r1_tarski @ X1 @ (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))))),
% 7.22/7.42      inference('demod', [status(thm)], ['75', '76'])).
% 7.22/7.42  thf('78', plain,
% 7.22/7.42      (((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 7.22/7.42         (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_A)))
% 7.22/7.42        | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 7.22/7.42      inference('sup-', [status(thm)], ['58', '77'])).
% 7.22/7.42  thf('79', plain, ((r1_tarski @ sk_C @ sk_A)),
% 7.22/7.42      inference('demod', [status(thm)], ['11', '12'])).
% 7.22/7.42  thf('80', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 7.22/7.42      inference('simplify', [status(thm)], ['19'])).
% 7.22/7.42  thf(t14_xboole_1, axiom,
% 7.22/7.42    (![A:$i,B:$i,C:$i]:
% 7.22/7.42     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 7.22/7.42         ( ![D:$i]:
% 7.22/7.42           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 7.22/7.42             ( r1_tarski @ B @ D ) ) ) ) =>
% 7.22/7.42       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 7.22/7.42  thf('81', plain,
% 7.22/7.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.22/7.42         (~ (r1_tarski @ X18 @ X19)
% 7.22/7.42          | ~ (r1_tarski @ X20 @ X19)
% 7.22/7.42          | (r1_tarski @ X18 @ (sk_D @ X20 @ X19 @ X18))
% 7.22/7.42          | ((X19) = (k2_xboole_0 @ X18 @ X20)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t14_xboole_1])).
% 7.22/7.42  thf('82', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 7.22/7.42          | (r1_tarski @ X0 @ (sk_D @ X1 @ X0 @ X0))
% 7.22/7.42          | ~ (r1_tarski @ X1 @ X0))),
% 7.22/7.42      inference('sup-', [status(thm)], ['80', '81'])).
% 7.22/7.42  thf('83', plain,
% 7.22/7.42      (((r1_tarski @ sk_A @ (sk_D @ sk_C @ sk_A @ sk_A))
% 7.22/7.42        | ((sk_A) = (k2_xboole_0 @ sk_A @ sk_C)))),
% 7.22/7.42      inference('sup-', [status(thm)], ['79', '82'])).
% 7.22/7.42  thf('84', plain,
% 7.22/7.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.22/7.42         (~ (r1_tarski @ X18 @ X19)
% 7.22/7.42          | ~ (r1_tarski @ X20 @ X19)
% 7.22/7.42          | ~ (r1_tarski @ X19 @ (sk_D @ X20 @ X19 @ X18))
% 7.22/7.42          | ((X19) = (k2_xboole_0 @ X18 @ X20)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t14_xboole_1])).
% 7.22/7.42  thf('85', plain,
% 7.22/7.42      ((((sk_A) = (k2_xboole_0 @ sk_A @ sk_C))
% 7.22/7.42        | ((sk_A) = (k2_xboole_0 @ sk_A @ sk_C))
% 7.22/7.42        | ~ (r1_tarski @ sk_C @ sk_A)
% 7.22/7.42        | ~ (r1_tarski @ sk_A @ sk_A))),
% 7.22/7.42      inference('sup-', [status(thm)], ['83', '84'])).
% 7.22/7.42  thf('86', plain, ((r1_tarski @ sk_C @ sk_A)),
% 7.22/7.42      inference('demod', [status(thm)], ['11', '12'])).
% 7.22/7.42  thf('87', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 7.22/7.42      inference('simplify', [status(thm)], ['19'])).
% 7.22/7.42  thf('88', plain,
% 7.22/7.42      ((((sk_A) = (k2_xboole_0 @ sk_A @ sk_C))
% 7.22/7.42        | ((sk_A) = (k2_xboole_0 @ sk_A @ sk_C)))),
% 7.22/7.42      inference('demod', [status(thm)], ['85', '86', '87'])).
% 7.22/7.42  thf('89', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_C))),
% 7.22/7.42      inference('simplify', [status(thm)], ['88'])).
% 7.22/7.42  thf('90', plain,
% 7.22/7.42      (![X37 : $i, X38 : $i]:
% 7.22/7.42         ((k3_xboole_0 @ X37 @ X38)
% 7.22/7.42           = (k5_xboole_0 @ X37 @ 
% 7.22/7.42              (k5_xboole_0 @ X38 @ (k2_xboole_0 @ X37 @ X38))))),
% 7.22/7.42      inference('demod', [status(thm)], ['34', '35'])).
% 7.22/7.42  thf('91', plain,
% 7.22/7.42      (((k3_xboole_0 @ sk_A @ sk_C)
% 7.22/7.42         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_C @ sk_A)))),
% 7.22/7.42      inference('sup+', [status(thm)], ['89', '90'])).
% 7.22/7.42  thf('92', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 7.22/7.42      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 7.22/7.42  thf('93', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 7.22/7.42      inference('simplify', [status(thm)], ['19'])).
% 7.22/7.42  thf('94', plain,
% 7.22/7.42      (![X21 : $i, X22 : $i]:
% 7.22/7.42         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 7.22/7.42      inference('cnf', [status(esa)], [t28_xboole_1])).
% 7.22/7.42  thf('95', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 7.22/7.42      inference('sup-', [status(thm)], ['93', '94'])).
% 7.22/7.42  thf(t100_xboole_1, axiom,
% 7.22/7.42    (![A:$i,B:$i]:
% 7.22/7.42     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 7.22/7.42  thf('96', plain,
% 7.22/7.42      (![X7 : $i, X8 : $i]:
% 7.22/7.42         ((k4_xboole_0 @ X7 @ X8)
% 7.22/7.42           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.22/7.42  thf('97', plain,
% 7.22/7.42      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 7.22/7.42      inference('sup+', [status(thm)], ['95', '96'])).
% 7.22/7.42  thf('98', plain,
% 7.22/7.42      (![X34 : $i, X35 : $i, X36 : $i]:
% 7.22/7.42         ((k5_xboole_0 @ (k5_xboole_0 @ X34 @ X35) @ X36)
% 7.22/7.42           = (k5_xboole_0 @ X34 @ (k5_xboole_0 @ X35 @ X36)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t91_xboole_1])).
% 7.22/7.42  thf('99', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 7.22/7.42           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 7.22/7.42      inference('sup+', [status(thm)], ['97', '98'])).
% 7.22/7.42  thf('100', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 7.22/7.42           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 7.22/7.42      inference('sup+', [status(thm)], ['92', '99'])).
% 7.22/7.42  thf('101', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 7.22/7.42      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 7.22/7.42  thf('102', plain,
% 7.22/7.42      (((k3_xboole_0 @ sk_A @ sk_C)
% 7.22/7.42         = (k5_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_A)))),
% 7.22/7.42      inference('demod', [status(thm)], ['91', '100', '101'])).
% 7.22/7.42  thf('103', plain, (((k2_xboole_0 @ sk_C @ sk_A) = (sk_A))),
% 7.22/7.42      inference('sup-', [status(thm)], ['13', '14'])).
% 7.22/7.42  thf('104', plain,
% 7.22/7.42      (![X37 : $i, X38 : $i]:
% 7.22/7.42         ((k3_xboole_0 @ X37 @ X38)
% 7.22/7.42           = (k5_xboole_0 @ X37 @ 
% 7.22/7.42              (k5_xboole_0 @ X38 @ (k2_xboole_0 @ X37 @ X38))))),
% 7.22/7.42      inference('demod', [status(thm)], ['34', '35'])).
% 7.22/7.42  thf('105', plain,
% 7.22/7.42      (((k3_xboole_0 @ sk_C @ sk_A)
% 7.22/7.42         = (k5_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_A @ sk_A)))),
% 7.22/7.42      inference('sup+', [status(thm)], ['103', '104'])).
% 7.22/7.42  thf('106', plain, ((r1_tarski @ sk_C @ sk_A)),
% 7.22/7.42      inference('demod', [status(thm)], ['11', '12'])).
% 7.22/7.42  thf('107', plain,
% 7.22/7.42      (![X21 : $i, X22 : $i]:
% 7.22/7.42         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 7.22/7.42      inference('cnf', [status(esa)], [t28_xboole_1])).
% 7.22/7.42  thf('108', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 7.22/7.42      inference('sup-', [status(thm)], ['106', '107'])).
% 7.22/7.42  thf('109', plain,
% 7.22/7.42      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 7.22/7.42      inference('sup+', [status(thm)], ['95', '96'])).
% 7.22/7.42  thf('110', plain,
% 7.22/7.42      (((sk_C) = (k5_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_A)))),
% 7.22/7.42      inference('demod', [status(thm)], ['105', '108', '109'])).
% 7.22/7.42  thf('111', plain, (((sk_C) = (k3_xboole_0 @ sk_A @ sk_C))),
% 7.22/7.42      inference('sup+', [status(thm)], ['102', '110'])).
% 7.22/7.42  thf('112', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 7.22/7.42      inference('simplify', [status(thm)], ['19'])).
% 7.22/7.42  thf('113', plain,
% 7.22/7.42      (![X16 : $i, X17 : $i]:
% 7.22/7.42         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 7.22/7.42      inference('cnf', [status(esa)], [t12_xboole_1])).
% 7.22/7.42  thf('114', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 7.22/7.42      inference('sup-', [status(thm)], ['112', '113'])).
% 7.22/7.42  thf('115', plain, ((r1_tarski @ sk_B @ sk_A)),
% 7.22/7.42      inference('demod', [status(thm)], ['65', '66'])).
% 7.22/7.42  thf('116', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 7.22/7.42          | (r1_tarski @ X0 @ (sk_D @ X1 @ X0 @ X0))
% 7.22/7.42          | ~ (r1_tarski @ X1 @ X0))),
% 7.22/7.42      inference('sup-', [status(thm)], ['80', '81'])).
% 7.22/7.42  thf('117', plain,
% 7.22/7.42      (((r1_tarski @ sk_A @ (sk_D @ sk_B @ sk_A @ sk_A))
% 7.22/7.42        | ((sk_A) = (k2_xboole_0 @ sk_A @ sk_B)))),
% 7.22/7.42      inference('sup-', [status(thm)], ['115', '116'])).
% 7.22/7.42  thf('118', plain,
% 7.22/7.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.22/7.42         (~ (r1_tarski @ X18 @ X19)
% 7.22/7.42          | ~ (r1_tarski @ X20 @ X19)
% 7.22/7.42          | ~ (r1_tarski @ X19 @ (sk_D @ X20 @ X19 @ X18))
% 7.22/7.42          | ((X19) = (k2_xboole_0 @ X18 @ X20)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t14_xboole_1])).
% 7.22/7.42  thf('119', plain,
% 7.22/7.42      ((((sk_A) = (k2_xboole_0 @ sk_A @ sk_B))
% 7.22/7.42        | ((sk_A) = (k2_xboole_0 @ sk_A @ sk_B))
% 7.22/7.42        | ~ (r1_tarski @ sk_B @ sk_A)
% 7.22/7.42        | ~ (r1_tarski @ sk_A @ sk_A))),
% 7.22/7.42      inference('sup-', [status(thm)], ['117', '118'])).
% 7.22/7.42  thf('120', plain, ((r1_tarski @ sk_B @ sk_A)),
% 7.22/7.42      inference('demod', [status(thm)], ['65', '66'])).
% 7.22/7.42  thf('121', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 7.22/7.42      inference('simplify', [status(thm)], ['19'])).
% 7.22/7.42  thf('122', plain,
% 7.22/7.42      ((((sk_A) = (k2_xboole_0 @ sk_A @ sk_B))
% 7.22/7.42        | ((sk_A) = (k2_xboole_0 @ sk_A @ sk_B)))),
% 7.22/7.42      inference('demod', [status(thm)], ['119', '120', '121'])).
% 7.22/7.42  thf('123', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_B))),
% 7.22/7.42      inference('simplify', [status(thm)], ['122'])).
% 7.22/7.42  thf('124', plain,
% 7.22/7.42      (![X37 : $i, X38 : $i]:
% 7.22/7.42         ((k3_xboole_0 @ X37 @ X38)
% 7.22/7.42           = (k5_xboole_0 @ X37 @ 
% 7.22/7.42              (k5_xboole_0 @ X38 @ (k2_xboole_0 @ X37 @ X38))))),
% 7.22/7.42      inference('demod', [status(thm)], ['34', '35'])).
% 7.22/7.42  thf('125', plain,
% 7.22/7.42      (((k3_xboole_0 @ sk_A @ sk_B)
% 7.22/7.42         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_A)))),
% 7.22/7.42      inference('sup+', [status(thm)], ['123', '124'])).
% 7.22/7.42  thf('126', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 7.22/7.42           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 7.22/7.42      inference('sup+', [status(thm)], ['92', '99'])).
% 7.22/7.42  thf('127', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 7.22/7.42      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 7.22/7.42  thf('128', plain,
% 7.22/7.42      (((k3_xboole_0 @ sk_A @ sk_B)
% 7.22/7.43         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_A)))),
% 7.22/7.43      inference('demod', [status(thm)], ['125', '126', '127'])).
% 7.22/7.43  thf('129', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 7.22/7.43      inference('sup-', [status(thm)], ['67', '68'])).
% 7.22/7.43  thf('130', plain,
% 7.22/7.43      (![X37 : $i, X38 : $i]:
% 7.22/7.43         ((k3_xboole_0 @ X37 @ X38)
% 7.22/7.43           = (k5_xboole_0 @ X37 @ 
% 7.22/7.43              (k5_xboole_0 @ X38 @ (k2_xboole_0 @ X37 @ X38))))),
% 7.22/7.43      inference('demod', [status(thm)], ['34', '35'])).
% 7.22/7.43  thf('131', plain,
% 7.22/7.43      (((k3_xboole_0 @ sk_B @ sk_A)
% 7.22/7.43         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A)))),
% 7.22/7.43      inference('sup+', [status(thm)], ['129', '130'])).
% 7.22/7.43  thf('132', plain, ((r1_tarski @ sk_B @ sk_A)),
% 7.22/7.43      inference('demod', [status(thm)], ['65', '66'])).
% 7.22/7.43  thf('133', plain,
% 7.22/7.43      (![X21 : $i, X22 : $i]:
% 7.22/7.43         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 7.22/7.43      inference('cnf', [status(esa)], [t28_xboole_1])).
% 7.22/7.43  thf('134', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 7.22/7.43      inference('sup-', [status(thm)], ['132', '133'])).
% 7.22/7.43  thf('135', plain,
% 7.22/7.43      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 7.22/7.43      inference('sup+', [status(thm)], ['95', '96'])).
% 7.22/7.43  thf('136', plain,
% 7.22/7.43      (((sk_B) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_A)))),
% 7.22/7.43      inference('demod', [status(thm)], ['131', '134', '135'])).
% 7.22/7.43  thf('137', plain, (((sk_B) = (k3_xboole_0 @ sk_A @ sk_B))),
% 7.22/7.43      inference('sup+', [status(thm)], ['128', '136'])).
% 7.22/7.43  thf('138', plain,
% 7.22/7.43      (![X7 : $i, X8 : $i]:
% 7.22/7.43         ((k4_xboole_0 @ X7 @ X8)
% 7.22/7.43           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 7.22/7.43      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.22/7.43  thf('139', plain,
% 7.22/7.43      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 7.22/7.43      inference('sup+', [status(thm)], ['137', '138'])).
% 7.22/7.43  thf('140', plain,
% 7.22/7.43      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 7.22/7.43      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 7.22/7.43  thf('141', plain,
% 7.22/7.43      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 7.22/7.43      inference('demod', [status(thm)], ['139', '140'])).
% 7.22/7.43  thf('142', plain, (((sk_C) = (k3_xboole_0 @ sk_A @ sk_C))),
% 7.22/7.43      inference('sup+', [status(thm)], ['102', '110'])).
% 7.22/7.43  thf('143', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 7.22/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.43  thf('144', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 7.22/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.43  thf('145', plain,
% 7.22/7.43      (![X45 : $i, X46 : $i]:
% 7.22/7.43         (((k3_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))
% 7.22/7.43          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45)))),
% 7.22/7.43      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.22/7.43  thf('146', plain,
% 7.22/7.43      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 7.22/7.43      inference('sup-', [status(thm)], ['144', '145'])).
% 7.22/7.43  thf('147', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 7.22/7.43      inference('demod', [status(thm)], ['143', '146'])).
% 7.22/7.43  thf('148', plain,
% 7.22/7.43      (![X7 : $i, X8 : $i]:
% 7.22/7.43         ((k4_xboole_0 @ X7 @ X8)
% 7.22/7.43           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 7.22/7.43      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.22/7.43  thf('149', plain,
% 7.22/7.43      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.22/7.43         ((r1_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14))
% 7.22/7.43          | ~ (r1_tarski @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 7.22/7.43      inference('cnf', [status(esa)], [t107_xboole_1])).
% 7.22/7.43  thf('150', plain,
% 7.22/7.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.22/7.43         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 7.22/7.43          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 7.22/7.43      inference('sup-', [status(thm)], ['148', '149'])).
% 7.22/7.43  thf('151', plain,
% 7.22/7.43      ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_C)))),
% 7.22/7.43      inference('sup-', [status(thm)], ['147', '150'])).
% 7.22/7.43  thf(symmetry_r1_xboole_0, axiom,
% 7.22/7.43    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 7.22/7.43  thf('152', plain,
% 7.22/7.43      (![X2 : $i, X3 : $i]:
% 7.22/7.43         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 7.22/7.43      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 7.22/7.43  thf('153', plain,
% 7.22/7.43      ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_C)) @ sk_B)),
% 7.22/7.43      inference('sup-', [status(thm)], ['151', '152'])).
% 7.22/7.43  thf('154', plain, (((sk_C) = (k3_xboole_0 @ sk_A @ sk_C))),
% 7.22/7.43      inference('sup+', [status(thm)], ['102', '110'])).
% 7.22/7.43  thf('155', plain, (((sk_C) = (k3_xboole_0 @ sk_A @ sk_C))),
% 7.22/7.43      inference('sup+', [status(thm)], ['102', '110'])).
% 7.22/7.43  thf('156', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 7.22/7.43      inference('demod', [status(thm)], ['153', '154', '155'])).
% 7.22/7.43  thf('157', plain, ((r1_tarski @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))),
% 7.22/7.43      inference('demod', [status(thm)],
% 7.22/7.43                ['78', '111', '114', '141', '142', '156'])).
% 7.22/7.43  thf('158', plain, ($false), inference('demod', [status(thm)], ['4', '157'])).
% 7.22/7.43  
% 7.22/7.43  % SZS output end Refutation
% 7.22/7.43  
% 7.22/7.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
