%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OeWojcPbLx

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:54 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 337 expanded)
%              Number of leaves         :   33 ( 116 expanded)
%              Depth                    :   17
%              Number of atoms          :  869 (2509 expanded)
%              Number of equality atoms :   94 ( 277 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ X35 )
      | ( r2_hidden @ X34 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X42: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('10',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( r1_tarski @ X30 @ X28 )
      | ( X29
       != ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ X30 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['10','12'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

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
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('40',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('46',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','49'])).

thf('51',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','50'])).

thf('52',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('53',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','49'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','59'])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('62',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['61','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('72',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('74',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('76',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('78',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['60','78'])).

thf('80',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('81',plain,(
    ! [X37: $i] :
      ( ( k2_subset_1 @ X37 )
      = X37 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('82',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('84',plain,(
    ! [X40: $i,X41: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X40 @ X41 ) @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('85',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('87',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k4_subset_1 @ X44 @ X43 @ X45 )
        = ( k2_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['82','89'])).

thf('91',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['79','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OeWojcPbLx
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:09:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.40/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.63  % Solved by: fo/fo7.sh
% 0.40/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.63  % done 361 iterations in 0.173s
% 0.40/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.63  % SZS output start Refutation
% 0.40/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.63  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.40/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.63  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.40/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.63  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.40/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.63  thf(t25_subset_1, conjecture,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.63       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.40/0.63         ( k2_subset_1 @ A ) ) ))).
% 0.40/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.63    (~( ![A:$i,B:$i]:
% 0.40/0.63        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.63          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.40/0.63            ( k2_subset_1 @ A ) ) ) )),
% 0.40/0.63    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.40/0.63  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(d5_subset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.63       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.40/0.63  thf('1', plain,
% 0.40/0.63      (![X38 : $i, X39 : $i]:
% 0.40/0.63         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 0.40/0.63          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.40/0.63  thf('2', plain,
% 0.40/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.63  thf(t98_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.40/0.63  thf('3', plain,
% 0.40/0.63      (![X20 : $i, X21 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ X20 @ X21)
% 0.40/0.63           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.40/0.63  thf('4', plain,
% 0.40/0.63      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.40/0.63         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['2', '3'])).
% 0.40/0.63  thf('5', plain,
% 0.40/0.63      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.40/0.63         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['2', '3'])).
% 0.40/0.63  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(d2_subset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( v1_xboole_0 @ A ) =>
% 0.40/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.40/0.63       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.40/0.63  thf('7', plain,
% 0.40/0.63      (![X34 : $i, X35 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X34 @ X35)
% 0.40/0.63          | (r2_hidden @ X34 @ X35)
% 0.40/0.63          | (v1_xboole_0 @ X35))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.40/0.63  thf('8', plain,
% 0.40/0.63      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.63        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.63  thf(fc1_subset_1, axiom,
% 0.40/0.63    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.63  thf('9', plain, (![X42 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X42))),
% 0.40/0.63      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.40/0.63  thf('10', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('clc', [status(thm)], ['8', '9'])).
% 0.40/0.63  thf(d1_zfmisc_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.40/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.40/0.63  thf('11', plain,
% 0.40/0.63      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.40/0.63         (~ (r2_hidden @ X30 @ X29)
% 0.40/0.63          | (r1_tarski @ X30 @ X28)
% 0.40/0.63          | ((X29) != (k1_zfmisc_1 @ X28)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.40/0.63  thf('12', plain,
% 0.40/0.63      (![X28 : $i, X30 : $i]:
% 0.40/0.63         ((r1_tarski @ X30 @ X28) | ~ (r2_hidden @ X30 @ (k1_zfmisc_1 @ X28)))),
% 0.40/0.63      inference('simplify', [status(thm)], ['11'])).
% 0.40/0.63  thf('13', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.40/0.63      inference('sup-', [status(thm)], ['10', '12'])).
% 0.40/0.63  thf(t28_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.63  thf('14', plain,
% 0.40/0.63      (![X12 : $i, X13 : $i]:
% 0.40/0.63         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.40/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.63  thf('15', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.63  thf('16', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.63  thf(t100_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.63  thf('17', plain,
% 0.40/0.63      (![X5 : $i, X6 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X5 @ X6)
% 0.40/0.63           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.63  thf('18', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.40/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['16', '17'])).
% 0.40/0.63  thf('19', plain,
% 0.40/0.63      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.63      inference('sup+', [status(thm)], ['15', '18'])).
% 0.40/0.63  thf('20', plain,
% 0.40/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.63  thf('21', plain,
% 0.40/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.63  thf(t91_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.40/0.63       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.40/0.63  thf('22', plain,
% 0.40/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.63         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.40/0.63           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.40/0.63  thf('23', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 0.40/0.63           = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ X0)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['21', '22'])).
% 0.40/0.63  thf('24', plain,
% 0.40/0.63      (((k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.40/0.63         (k3_subset_1 @ sk_A @ sk_B))
% 0.40/0.63         = (k5_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['5', '23'])).
% 0.40/0.63  thf(d10_xboole_0, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.63  thf('25', plain,
% 0.40/0.63      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.63  thf('26', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.40/0.63      inference('simplify', [status(thm)], ['25'])).
% 0.40/0.63  thf('27', plain,
% 0.40/0.63      (![X12 : $i, X13 : $i]:
% 0.40/0.63         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.40/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.63  thf('28', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.63  thf('29', plain,
% 0.40/0.63      (![X5 : $i, X6 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X5 @ X6)
% 0.40/0.63           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.63  thf('30', plain,
% 0.40/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['28', '29'])).
% 0.40/0.63  thf(t22_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.40/0.63  thf('31', plain,
% 0.40/0.63      (![X10 : $i, X11 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.40/0.63      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.40/0.63  thf(t46_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.40/0.63  thf('32', plain,
% 0.40/0.63      (![X14 : $i, X15 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 0.40/0.63      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.40/0.63  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['31', '32'])).
% 0.40/0.63  thf('34', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['30', '33'])).
% 0.40/0.63  thf('35', plain,
% 0.40/0.63      (((k1_xboole_0) = (k5_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.40/0.63      inference('demod', [status(thm)], ['24', '34'])).
% 0.40/0.63  thf('36', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['30', '33'])).
% 0.40/0.63  thf('37', plain,
% 0.40/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.63         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.40/0.63           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.40/0.63  thf('38', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.40/0.63           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['36', '37'])).
% 0.40/0.63  thf('39', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['30', '33'])).
% 0.40/0.63  thf(t112_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.40/0.63       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.40/0.63  thf('40', plain,
% 0.40/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.63         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 0.40/0.63           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 0.40/0.63      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.40/0.63  thf('41', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k1_xboole_0) = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['39', '40'])).
% 0.40/0.63  thf('42', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['30', '33'])).
% 0.40/0.63  thf('43', plain,
% 0.40/0.63      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.63  thf('44', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.40/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['16', '17'])).
% 0.40/0.63  thf('45', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['43', '44'])).
% 0.40/0.63  thf(t5_boole, axiom,
% 0.40/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.63  thf('46', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.40/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.63  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['45', '46'])).
% 0.40/0.63  thf('48', plain,
% 0.40/0.63      (![X20 : $i, X21 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ X20 @ X21)
% 0.40/0.63           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.40/0.63  thf('49', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['47', '48'])).
% 0.40/0.63  thf('50', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.40/0.63           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.40/0.63      inference('demod', [status(thm)], ['38', '49'])).
% 0.40/0.63  thf('51', plain,
% 0.40/0.63      (((k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.40/0.63         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['35', '50'])).
% 0.40/0.63  thf('52', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.40/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.63  thf('53', plain,
% 0.40/0.63      (((k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A)) = (sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['51', '52'])).
% 0.40/0.63  thf('54', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['30', '33'])).
% 0.40/0.63  thf('55', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.40/0.63           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.40/0.63      inference('demod', [status(thm)], ['38', '49'])).
% 0.40/0.63  thf('56', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['54', '55'])).
% 0.40/0.63  thf('57', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.40/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.63  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['56', '57'])).
% 0.40/0.63  thf('59', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['53', '58'])).
% 0.40/0.63  thf('60', plain,
% 0.40/0.63      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.40/0.63      inference('demod', [status(thm)], ['4', '59'])).
% 0.40/0.63  thf('61', plain,
% 0.40/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.63  thf('62', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.63  thf('63', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.63  thf('64', plain,
% 0.40/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.63         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 0.40/0.63           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 0.40/0.63      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.40/0.63  thf('65', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.63         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 0.40/0.63           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 0.40/0.63      inference('sup+', [status(thm)], ['63', '64'])).
% 0.40/0.63  thf('66', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 0.40/0.63           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.40/0.63      inference('sup+', [status(thm)], ['62', '65'])).
% 0.40/0.63  thf('67', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.40/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['16', '17'])).
% 0.40/0.63  thf('68', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.63  thf('69', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ sk_B @ X0)
% 0.40/0.63           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.40/0.63      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.40/0.63  thf('70', plain,
% 0.40/0.63      (((k4_xboole_0 @ sk_B @ sk_B)
% 0.40/0.63         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['61', '69'])).
% 0.40/0.63  thf('71', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['31', '32'])).
% 0.40/0.63  thf('72', plain,
% 0.40/0.63      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.40/0.63      inference('demod', [status(thm)], ['70', '71'])).
% 0.40/0.63  thf('73', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.40/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['16', '17'])).
% 0.40/0.63  thf('74', plain,
% 0.40/0.63      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.40/0.63         = (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ k1_xboole_0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['72', '73'])).
% 0.40/0.63  thf('75', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.40/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.63  thf('76', plain,
% 0.40/0.63      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.40/0.63         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.40/0.63      inference('demod', [status(thm)], ['74', '75'])).
% 0.40/0.63  thf('77', plain,
% 0.40/0.63      (![X20 : $i, X21 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ X20 @ X21)
% 0.40/0.63           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.40/0.63  thf('78', plain,
% 0.40/0.63      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.40/0.63         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['76', '77'])).
% 0.40/0.63  thf('79', plain,
% 0.40/0.63      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.40/0.63      inference('sup+', [status(thm)], ['60', '78'])).
% 0.40/0.63  thf('80', plain,
% 0.40/0.63      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.40/0.63         != (k2_subset_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.40/0.63  thf('81', plain, (![X37 : $i]: ((k2_subset_1 @ X37) = (X37))),
% 0.40/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.40/0.63  thf('82', plain,
% 0.40/0.63      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['80', '81'])).
% 0.40/0.63  thf('83', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(dt_k3_subset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.63       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.63  thf('84', plain,
% 0.40/0.63      (![X40 : $i, X41 : $i]:
% 0.40/0.63         ((m1_subset_1 @ (k3_subset_1 @ X40 @ X41) @ (k1_zfmisc_1 @ X40))
% 0.40/0.63          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40)))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.40/0.63  thf('85', plain,
% 0.40/0.63      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('sup-', [status(thm)], ['83', '84'])).
% 0.40/0.63  thf('86', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(redefinition_k4_subset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.40/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.63       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.40/0.63  thf('87', plain,
% 0.40/0.63      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.40/0.63          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X44))
% 0.40/0.63          | ((k4_subset_1 @ X44 @ X43 @ X45) = (k2_xboole_0 @ X43 @ X45)))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.40/0.63  thf('88', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.40/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['86', '87'])).
% 0.40/0.63  thf('89', plain,
% 0.40/0.63      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.40/0.63         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['85', '88'])).
% 0.40/0.63  thf('90', plain,
% 0.40/0.63      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['82', '89'])).
% 0.40/0.63  thf('91', plain, ($false),
% 0.40/0.63      inference('simplify_reflect-', [status(thm)], ['79', '90'])).
% 0.40/0.63  
% 0.40/0.63  % SZS output end Refutation
% 0.40/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
