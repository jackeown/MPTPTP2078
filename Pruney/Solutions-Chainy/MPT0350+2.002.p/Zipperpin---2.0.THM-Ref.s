%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ckqeTauDIs

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:45 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 595 expanded)
%              Number of leaves         :   38 ( 205 expanded)
%              Depth                    :   17
%              Number of atoms          : 1202 (4434 expanded)
%              Number of equality atoms :  128 ( 438 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
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

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('13',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ X35 )
      | ( r2_hidden @ X34 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X42: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('20',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('21',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( r1_tarski @ X30 @ X28 )
      | ( X29
       != ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('22',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ X30 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['20','22'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('29',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

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
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('33',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('41',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45','50'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','32','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('60',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_A )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','58','59'])).

thf('61',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_B )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','60'])).

thf('62',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

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
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','69','70'])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['61','71'])).

thf('73',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('74',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ( r2_hidden @ X27 @ X29 )
      | ( X29
       != ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('75',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ( m1_subset_1 @ X34 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X42: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('81',plain,(
    ! [X40: $i,X41: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X40 @ X41 ) @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('84',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45','50'])).

thf('87',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','90','93'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('95',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('96',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('98',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('99',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('101',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('103',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf('105',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('107',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('109',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('111',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf('112',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('115',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('117',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('118',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('120',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','118','119'])).

thf('121',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('122',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['96','120','121'])).

thf('123',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('124',plain,(
    ! [X37: $i] :
      ( ( k2_subset_1 @ X37 )
      = X37 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('125',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X40: $i,X41: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X40 @ X41 ) @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('128',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('130',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k4_subset_1 @ X44 @ X43 @ X45 )
        = ( k2_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','131'])).

thf('133',plain,(
    ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['125','132'])).

thf('134',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['122','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ckqeTauDIs
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:35:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 342 iterations in 0.124s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.59  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(t25_subset_1, conjecture,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.59       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.37/0.59         ( k2_subset_1 @ A ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i,B:$i]:
% 0.37/0.59        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.59          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.37/0.59            ( k2_subset_1 @ A ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.37/0.59  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(d5_subset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.59       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.37/0.59  thf('1', plain,
% 0.37/0.59      (![X38 : $i, X39 : $i]:
% 0.37/0.59         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 0.37/0.59          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.59  thf(d6_xboole_0, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( k5_xboole_0 @ A @ B ) =
% 0.37/0.59       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      (![X2 : $i, X3 : $i]:
% 0.37/0.59         ((k5_xboole_0 @ X2 @ X3)
% 0.37/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.37/0.59  thf('4', plain,
% 0.37/0.59      (((k5_xboole_0 @ sk_B @ sk_A)
% 0.37/0.59         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 0.37/0.59            (k3_subset_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.59  thf(commutativity_k2_tarski, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      (![X20 : $i, X21 : $i]:
% 0.37/0.59         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 0.37/0.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.59  thf(l51_zfmisc_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (![X32 : $i, X33 : $i]:
% 0.37/0.59         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 0.37/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      (![X32 : $i, X33 : $i]:
% 0.37/0.59         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 0.37/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.59  thf('9', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.59  thf('10', plain,
% 0.37/0.59      (((k5_xboole_0 @ sk_B @ sk_A)
% 0.37/0.59         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.37/0.59            (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.37/0.59      inference('demod', [status(thm)], ['4', '9'])).
% 0.37/0.59  thf('11', plain,
% 0.37/0.59      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      (![X2 : $i, X3 : $i]:
% 0.37/0.59         ((k5_xboole_0 @ X2 @ X3)
% 0.37/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.37/0.59  thf('13', plain,
% 0.37/0.59      (((k5_xboole_0 @ sk_A @ sk_B)
% 0.37/0.59         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.37/0.59            (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.59  thf('14', plain,
% 0.37/0.59      (((k5_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.37/0.59      inference('sup+', [status(thm)], ['10', '13'])).
% 0.37/0.59  thf('15', plain,
% 0.37/0.59      (((k5_xboole_0 @ sk_B @ sk_A)
% 0.37/0.59         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.37/0.59            (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.37/0.59      inference('demod', [status(thm)], ['4', '9'])).
% 0.37/0.59  thf('16', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(d2_subset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( v1_xboole_0 @ A ) =>
% 0.37/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.37/0.59       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.59  thf('17', plain,
% 0.37/0.59      (![X34 : $i, X35 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X34 @ X35)
% 0.37/0.59          | (r2_hidden @ X34 @ X35)
% 0.37/0.59          | (v1_xboole_0 @ X35))),
% 0.37/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.37/0.59  thf('18', plain,
% 0.37/0.59      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.59        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.59  thf(fc1_subset_1, axiom,
% 0.37/0.59    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.59  thf('19', plain, (![X42 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X42))),
% 0.37/0.59      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.37/0.59  thf('20', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.59      inference('clc', [status(thm)], ['18', '19'])).
% 0.37/0.59  thf(d1_zfmisc_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.37/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.37/0.59  thf('21', plain,
% 0.37/0.59      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X30 @ X29)
% 0.37/0.59          | (r1_tarski @ X30 @ X28)
% 0.37/0.59          | ((X29) != (k1_zfmisc_1 @ X28)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.37/0.59  thf('22', plain,
% 0.37/0.59      (![X28 : $i, X30 : $i]:
% 0.37/0.59         ((r1_tarski @ X30 @ X28) | ~ (r2_hidden @ X30 @ (k1_zfmisc_1 @ X28)))),
% 0.37/0.59      inference('simplify', [status(thm)], ['21'])).
% 0.37/0.59  thf('23', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.37/0.59      inference('sup-', [status(thm)], ['20', '22'])).
% 0.37/0.59  thf(t28_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.59  thf('24', plain,
% 0.37/0.59      (![X12 : $i, X13 : $i]:
% 0.37/0.59         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.37/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.59  thf('25', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.59  thf(t100_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.59  thf('26', plain,
% 0.37/0.59      (![X5 : $i, X6 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.59           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.59  thf('27', plain,
% 0.37/0.59      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.37/0.59      inference('sup+', [status(thm)], ['25', '26'])).
% 0.37/0.59  thf('28', plain,
% 0.37/0.59      (![X2 : $i, X3 : $i]:
% 0.37/0.59         ((k5_xboole_0 @ X2 @ X3)
% 0.37/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.37/0.59  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.59  thf('29', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.37/0.59      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.59  thf(t22_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.37/0.59  thf('30', plain,
% 0.37/0.59      (![X10 : $i, X11 : $i]:
% 0.37/0.59         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.37/0.59      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.37/0.59  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['29', '30'])).
% 0.37/0.59  thf('32', plain,
% 0.37/0.59      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['28', '31'])).
% 0.37/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.59  thf('33', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.37/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.59  thf('34', plain,
% 0.37/0.59      (![X12 : $i, X13 : $i]:
% 0.37/0.59         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.37/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.59  thf('35', plain,
% 0.37/0.59      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.59  thf('36', plain,
% 0.37/0.59      (![X5 : $i, X6 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.59           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.59  thf('37', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.59           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.59  thf('38', plain,
% 0.37/0.59      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['28', '31'])).
% 0.37/0.59  thf('39', plain,
% 0.37/0.59      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['28', '31'])).
% 0.37/0.59  thf(t5_boole, axiom,
% 0.37/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.59  thf('40', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.37/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.59  thf('41', plain,
% 0.37/0.59      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['39', '40'])).
% 0.37/0.59  thf('42', plain,
% 0.37/0.59      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['37', '38', '41'])).
% 0.37/0.59  thf('43', plain,
% 0.37/0.59      (![X2 : $i, X3 : $i]:
% 0.37/0.59         ((k5_xboole_0 @ X2 @ X3)
% 0.37/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.37/0.59  thf('44', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.37/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['42', '43'])).
% 0.37/0.59  thf('45', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.37/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.59  thf('46', plain,
% 0.37/0.59      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.59  thf('47', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.59  thf('48', plain,
% 0.37/0.59      (![X10 : $i, X11 : $i]:
% 0.37/0.59         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.37/0.59      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.37/0.59  thf('49', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['47', '48'])).
% 0.37/0.59  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['46', '49'])).
% 0.37/0.59  thf('51', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['44', '45', '50'])).
% 0.37/0.59  thf(t48_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.59  thf('52', plain,
% 0.37/0.59      (![X15 : $i, X16 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.37/0.59           = (k3_xboole_0 @ X15 @ X16))),
% 0.37/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.59  thf('53', plain,
% 0.37/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['51', '52'])).
% 0.37/0.59  thf('54', plain,
% 0.37/0.59      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.59  thf('55', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.59  thf('56', plain,
% 0.37/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['54', '55'])).
% 0.37/0.59  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['53', '56'])).
% 0.37/0.59  thf('58', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['27', '32', '57'])).
% 0.37/0.59  thf('59', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['46', '49'])).
% 0.37/0.59  thf('60', plain,
% 0.37/0.59      (((k5_xboole_0 @ sk_B @ sk_A) = (k3_subset_1 @ sk_A @ sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['15', '58', '59'])).
% 0.37/0.59  thf('61', plain,
% 0.37/0.59      (((k5_xboole_0 @ sk_A @ sk_B) = (k3_subset_1 @ sk_A @ sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['14', '60'])).
% 0.37/0.59  thf('62', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.59  thf('63', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.59  thf(t112_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.37/0.59       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.37/0.59  thf('64', plain,
% 0.37/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.59         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 0.37/0.59           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 0.37/0.59      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.37/0.59  thf('65', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 0.37/0.59           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['63', '64'])).
% 0.37/0.59  thf('66', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 0.37/0.59           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.37/0.59      inference('sup+', [status(thm)], ['62', '65'])).
% 0.37/0.59  thf('67', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.59  thf('68', plain,
% 0.37/0.59      (![X5 : $i, X6 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.59           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.59  thf('69', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['67', '68'])).
% 0.37/0.59  thf('70', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.59  thf('71', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ sk_B @ X0)
% 0.37/0.59           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.37/0.59      inference('demod', [status(thm)], ['66', '69', '70'])).
% 0.37/0.59  thf('72', plain,
% 0.37/0.59      (((k4_xboole_0 @ sk_B @ sk_B)
% 0.37/0.59         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['61', '71'])).
% 0.37/0.59  thf('73', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.37/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.59  thf('74', plain,
% 0.37/0.59      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.59         (~ (r1_tarski @ X27 @ X28)
% 0.37/0.59          | (r2_hidden @ X27 @ X29)
% 0.37/0.59          | ((X29) != (k1_zfmisc_1 @ X28)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.37/0.59  thf('75', plain,
% 0.37/0.59      (![X27 : $i, X28 : $i]:
% 0.37/0.59         ((r2_hidden @ X27 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X27 @ X28))),
% 0.37/0.59      inference('simplify', [status(thm)], ['74'])).
% 0.37/0.59  thf('76', plain,
% 0.37/0.59      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['73', '75'])).
% 0.37/0.59  thf('77', plain,
% 0.37/0.59      (![X34 : $i, X35 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X34 @ X35)
% 0.37/0.59          | (m1_subset_1 @ X34 @ X35)
% 0.37/0.59          | (v1_xboole_0 @ X35))),
% 0.37/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.37/0.59  thf('78', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.37/0.59          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['76', '77'])).
% 0.37/0.59  thf('79', plain, (![X42 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X42))),
% 0.37/0.59      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.37/0.59  thf('80', plain,
% 0.37/0.59      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.59      inference('clc', [status(thm)], ['78', '79'])).
% 0.37/0.59  thf(dt_k3_subset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.59       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.59  thf('81', plain,
% 0.37/0.59      (![X40 : $i, X41 : $i]:
% 0.37/0.59         ((m1_subset_1 @ (k3_subset_1 @ X40 @ X41) @ (k1_zfmisc_1 @ X40))
% 0.37/0.59          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40)))),
% 0.37/0.59      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.37/0.59  thf('82', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['80', '81'])).
% 0.37/0.59  thf('83', plain,
% 0.37/0.59      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.59      inference('clc', [status(thm)], ['78', '79'])).
% 0.37/0.59  thf('84', plain,
% 0.37/0.59      (![X38 : $i, X39 : $i]:
% 0.37/0.59         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 0.37/0.59          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.59  thf('85', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['83', '84'])).
% 0.37/0.59  thf('86', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['44', '45', '50'])).
% 0.37/0.59  thf('87', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['85', '86'])).
% 0.37/0.59  thf('88', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.59      inference('demod', [status(thm)], ['82', '87'])).
% 0.37/0.59  thf('89', plain,
% 0.37/0.59      (![X38 : $i, X39 : $i]:
% 0.37/0.59         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 0.37/0.59          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.59  thf('90', plain,
% 0.37/0.59      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['88', '89'])).
% 0.37/0.59  thf('91', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['53', '56'])).
% 0.37/0.59  thf('92', plain,
% 0.37/0.59      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['88', '89'])).
% 0.37/0.59  thf('93', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['91', '92'])).
% 0.37/0.59  thf('94', plain,
% 0.37/0.59      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['72', '90', '93'])).
% 0.37/0.59  thf(t94_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( k2_xboole_0 @ A @ B ) =
% 0.37/0.59       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.59  thf('95', plain,
% 0.37/0.59      (![X18 : $i, X19 : $i]:
% 0.37/0.59         ((k2_xboole_0 @ X18 @ X19)
% 0.37/0.59           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.37/0.59              (k3_xboole_0 @ X18 @ X19)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.37/0.59  thf('96', plain,
% 0.37/0.59      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.37/0.59         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 0.37/0.59            k1_xboole_0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['94', '95'])).
% 0.37/0.59  thf('97', plain,
% 0.37/0.59      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.59  thf('98', plain,
% 0.37/0.59      (![X15 : $i, X16 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.37/0.59           = (k3_xboole_0 @ X15 @ X16))),
% 0.37/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.59  thf('99', plain,
% 0.37/0.59      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.37/0.59         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.59      inference('sup+', [status(thm)], ['97', '98'])).
% 0.37/0.59  thf('100', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.59  thf('101', plain,
% 0.37/0.59      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.37/0.59         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.37/0.59      inference('demod', [status(thm)], ['99', '100'])).
% 0.37/0.59  thf('102', plain,
% 0.37/0.59      (![X15 : $i, X16 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.37/0.59           = (k3_xboole_0 @ X15 @ X16))),
% 0.37/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.59  thf('103', plain,
% 0.37/0.59      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.37/0.59         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['101', '102'])).
% 0.37/0.59  thf('104', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.59  thf('105', plain,
% 0.37/0.59      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.37/0.59         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['103', '104'])).
% 0.37/0.59  thf('106', plain,
% 0.37/0.59      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.59  thf('107', plain,
% 0.37/0.59      (((k3_subset_1 @ sk_A @ sk_B)
% 0.37/0.59         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['105', '106'])).
% 0.37/0.59  thf('108', plain,
% 0.37/0.59      (![X5 : $i, X6 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.59           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.59  thf('109', plain,
% 0.37/0.59      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.37/0.59         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['107', '108'])).
% 0.37/0.59  thf('110', plain,
% 0.37/0.59      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.37/0.59         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.37/0.59      inference('demod', [status(thm)], ['99', '100'])).
% 0.37/0.59  thf('111', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.59  thf('112', plain,
% 0.37/0.59      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['110', '111'])).
% 0.37/0.59  thf('113', plain,
% 0.37/0.59      (((sk_B) = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['109', '112'])).
% 0.37/0.59  thf('114', plain,
% 0.37/0.59      (![X18 : $i, X19 : $i]:
% 0.37/0.59         ((k2_xboole_0 @ X18 @ X19)
% 0.37/0.59           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.37/0.59              (k3_xboole_0 @ X18 @ X19)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.37/0.59  thf('115', plain,
% 0.37/0.59      (((k2_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.37/0.59         = (k5_xboole_0 @ sk_B @ 
% 0.37/0.59            (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.37/0.59      inference('sup+', [status(thm)], ['113', '114'])).
% 0.37/0.59  thf('116', plain,
% 0.37/0.59      (((k3_subset_1 @ sk_A @ sk_B)
% 0.37/0.59         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['105', '106'])).
% 0.37/0.59  thf('117', plain,
% 0.37/0.59      (![X10 : $i, X11 : $i]:
% 0.37/0.59         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.37/0.59      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.37/0.59  thf('118', plain,
% 0.37/0.59      (((k2_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.37/0.59      inference('sup+', [status(thm)], ['116', '117'])).
% 0.37/0.59  thf('119', plain,
% 0.37/0.59      (((k3_subset_1 @ sk_A @ sk_B)
% 0.37/0.59         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['105', '106'])).
% 0.37/0.59  thf('120', plain,
% 0.37/0.59      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['115', '118', '119'])).
% 0.37/0.59  thf('121', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.37/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.59  thf('122', plain,
% 0.37/0.59      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.37/0.59      inference('demod', [status(thm)], ['96', '120', '121'])).
% 0.37/0.59  thf('123', plain,
% 0.37/0.59      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.37/0.59         != (k2_subset_1 @ sk_A))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.37/0.59  thf('124', plain, (![X37 : $i]: ((k2_subset_1 @ X37) = (X37))),
% 0.37/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.37/0.59  thf('125', plain,
% 0.37/0.59      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.37/0.59      inference('demod', [status(thm)], ['123', '124'])).
% 0.37/0.59  thf('126', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('127', plain,
% 0.37/0.59      (![X40 : $i, X41 : $i]:
% 0.37/0.59         ((m1_subset_1 @ (k3_subset_1 @ X40 @ X41) @ (k1_zfmisc_1 @ X40))
% 0.37/0.59          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40)))),
% 0.37/0.59      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.37/0.59  thf('128', plain,
% 0.37/0.59      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['126', '127'])).
% 0.37/0.59  thf('129', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(redefinition_k4_subset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.37/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.59       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.59  thf('130', plain,
% 0.37/0.59      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.37/0.59          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X44))
% 0.37/0.59          | ((k4_subset_1 @ X44 @ X43 @ X45) = (k2_xboole_0 @ X43 @ X45)))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.37/0.59  thf('131', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.37/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['129', '130'])).
% 0.37/0.59  thf('132', plain,
% 0.37/0.59      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.37/0.59         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['128', '131'])).
% 0.37/0.59  thf('133', plain,
% 0.37/0.59      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.37/0.59      inference('demod', [status(thm)], ['125', '132'])).
% 0.37/0.59  thf('134', plain, ($false),
% 0.37/0.59      inference('simplify_reflect-', [status(thm)], ['122', '133'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
