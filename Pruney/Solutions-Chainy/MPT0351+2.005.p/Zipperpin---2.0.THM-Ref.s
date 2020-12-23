%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nUMqvfnWyI

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 310 expanded)
%              Number of leaves         :   32 ( 110 expanded)
%              Depth                    :   17
%              Number of atoms          :  657 (2017 expanded)
%              Number of equality atoms :   68 ( 165 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('0',plain,(
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

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X27: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r1_tarski @ X18 @ X16 )
      | ( X17
       != ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X27: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X26 ) @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('42',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('43',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X27: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['40','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','58'])).

thf('60',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('62',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('68',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['19','66','67'])).

thf('69',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('71',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('72',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('75',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k4_subset_1 @ X29 @ X28 @ X30 )
        = ( k2_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['72','77'])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nUMqvfnWyI
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:25:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 128 iterations in 0.047s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(t28_subset_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.21/0.51  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d2_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X22 : $i, X23 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X22 @ X23)
% 0.21/0.51          | (r2_hidden @ X22 @ X23)
% 0.21/0.51          | (v1_xboole_0 @ X23))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.51        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf(fc1_subset_1, axiom,
% 0.21/0.51    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.51  thf('3', plain, (![X27 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.51  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf(d1_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X18 @ X17)
% 0.21/0.51          | (r1_tarski @ X18 @ X16)
% 0.21/0.51          | ((X17) != (k1_zfmisc_1 @ X16)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X16 : $i, X18 : $i]:
% 0.21/0.51         ((r1_tarski @ X18 @ X16) | ~ (r2_hidden @ X18 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.51  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.51  thf(t28_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.51  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf(t100_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.51           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.21/0.51      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf(t98_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ X9 @ X10)
% 0.21/0.52           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.21/0.52         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf(commutativity_k2_tarski, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i]:
% 0.21/0.52         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.52  thf(l51_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         ((k3_tarski @ (k2_tarski @ X20 @ X21)) = (k2_xboole_0 @ X20 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         ((k3_tarski @ (k2_tarski @ X20 @ X21)) = (k2_xboole_0 @ X20 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.21/0.52         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['13', '18'])).
% 0.21/0.52  thf(t4_subset_1, axiom,
% 0.21/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X31 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X22 : $i, X23 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X22 @ X23)
% 0.21/0.52          | (r2_hidden @ X22 @ X23)
% 0.21/0.52          | (v1_xboole_0 @ X23))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.21/0.52          | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain, (![X27 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.52      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X16 : $i, X18 : $i]:
% 0.21/0.52         ((r1_tarski @ X18 @ X16) | ~ (r2_hidden @ X18 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.52  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.52           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf(t48_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.21/0.52           = (k3_xboole_0 @ X7 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.21/0.52           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.52           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.52           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.52           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf(dt_k2_subset_1, axiom,
% 0.21/0.52    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X26 : $i]: (m1_subset_1 @ (k2_subset_1 @ X26) @ (k1_zfmisc_1 @ X26))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.52  thf('42', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.52  thf('43', plain, (![X26 : $i]: (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X26))),
% 0.21/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X22 : $i, X23 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X22 @ X23)
% 0.21/0.52          | (r2_hidden @ X22 @ X23)
% 0.21/0.52          | (v1_xboole_0 @ X23))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.21/0.52          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('46', plain, (![X27 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.52  thf('47', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.52      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X16 : $i, X18 : $i]:
% 0.21/0.52         ((r1_tarski @ X18 @ X16) | ~ (r2_hidden @ X18 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.52  thf('49', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.52  thf('51', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.52           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['51', '52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.21/0.52           = (k3_xboole_0 @ X7 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.21/0.52           = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['53', '54'])).
% 0.21/0.52  thf('56', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['40', '57'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['39', '58'])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ X9 @ X10)
% 0.21/0.52           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['59', '60'])).
% 0.21/0.52  thf(t1_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.52  thf('62', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.52  thf('63', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['61', '62'])).
% 0.21/0.52  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['36', '63'])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['51', '52'])).
% 0.21/0.52  thf('66', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['64', '65'])).
% 0.21/0.52  thf('67', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['61', '62'])).
% 0.21/0.52  thf('68', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['19', '66', '67'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.21/0.52         != (k2_subset_1 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('70', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.52  thf('71', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.52  thf('72', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.21/0.52  thf('73', plain, (![X26 : $i]: (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X26))),
% 0.21/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf('74', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k4_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.52       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.21/0.52          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 0.21/0.52          | ((k4_subset_1 @ X29 @ X28 @ X30) = (k2_xboole_0 @ X28 @ X30)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['73', '76'])).
% 0.21/0.52  thf('78', plain, (((k2_xboole_0 @ sk_B @ sk_A) != (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['72', '77'])).
% 0.21/0.52  thf('79', plain, ($false),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['68', '78'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
