%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BMmIX5ctUH

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:54 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 265 expanded)
%              Number of leaves         :   32 (  92 expanded)
%              Depth                    :   14
%              Number of atoms          :  731 (2130 expanded)
%              Number of equality atoms :   73 ( 182 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ( r2_hidden @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X41: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X41 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( r1_tarski @ X29 @ X27 )
      | ( X28
       != ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ X29 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
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
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X37 @ X38 )
        = ( k4_xboole_0 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','25'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('32',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('43',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('51',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('54',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('56',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','54','55'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('57',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('58',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['32','56','57'])).

thf('59',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('60',plain,(
    ! [X36: $i] :
      ( ( k2_subset_1 @ X36 )
      = X36 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('61',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('63',plain,(
    ! [X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('64',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('66',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k4_subset_1 @ X43 @ X42 @ X44 )
        = ( k2_xboole_0 @ X42 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['61','68'])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BMmIX5ctUH
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:54:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.56  % Solved by: fo/fo7.sh
% 0.19/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.56  % done 267 iterations in 0.115s
% 0.19/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.56  % SZS output start Refutation
% 0.19/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.56  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.19/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.56  thf(t25_subset_1, conjecture,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.56       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.19/0.56         ( k2_subset_1 @ A ) ) ))).
% 0.19/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.56    (~( ![A:$i,B:$i]:
% 0.19/0.56        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.56          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.19/0.56            ( k2_subset_1 @ A ) ) ) )),
% 0.19/0.56    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.19/0.56  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(d2_subset_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.56       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.56  thf('1', plain,
% 0.19/0.56      (![X33 : $i, X34 : $i]:
% 0.19/0.56         (~ (m1_subset_1 @ X33 @ X34)
% 0.19/0.56          | (r2_hidden @ X33 @ X34)
% 0.19/0.56          | (v1_xboole_0 @ X34))),
% 0.19/0.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.56  thf('2', plain,
% 0.19/0.56      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.56        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.56  thf(fc1_subset_1, axiom,
% 0.19/0.56    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.56  thf('3', plain, (![X41 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X41))),
% 0.19/0.56      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.56  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.56      inference('clc', [status(thm)], ['2', '3'])).
% 0.19/0.56  thf(d1_zfmisc_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.56  thf('5', plain,
% 0.19/0.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.56         (~ (r2_hidden @ X29 @ X28)
% 0.19/0.56          | (r1_tarski @ X29 @ X27)
% 0.19/0.56          | ((X28) != (k1_zfmisc_1 @ X27)))),
% 0.19/0.56      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.56  thf('6', plain,
% 0.19/0.56      (![X27 : $i, X29 : $i]:
% 0.19/0.56         ((r1_tarski @ X29 @ X27) | ~ (r2_hidden @ X29 @ (k1_zfmisc_1 @ X27)))),
% 0.19/0.56      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.56  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.56      inference('sup-', [status(thm)], ['4', '6'])).
% 0.19/0.56  thf(t28_xboole_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.56  thf('8', plain,
% 0.19/0.56      (![X12 : $i, X13 : $i]:
% 0.19/0.56         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.19/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.56  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.19/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.56  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.56  thf('10', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.56  thf(t100_xboole_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.56  thf('11', plain,
% 0.19/0.56      (![X5 : $i, X6 : $i]:
% 0.19/0.56         ((k4_xboole_0 @ X5 @ X6)
% 0.19/0.56           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.19/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.56  thf('12', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         ((k4_xboole_0 @ X0 @ X1)
% 0.19/0.56           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.56      inference('sup+', [status(thm)], ['10', '11'])).
% 0.19/0.56  thf('13', plain,
% 0.19/0.56      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.56      inference('sup+', [status(thm)], ['9', '12'])).
% 0.19/0.56  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(d5_subset_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.56       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.56  thf('15', plain,
% 0.19/0.56      (![X37 : $i, X38 : $i]:
% 0.19/0.56         (((k3_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))
% 0.19/0.56          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 0.19/0.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.56  thf('16', plain,
% 0.19/0.56      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.56  thf('17', plain,
% 0.19/0.56      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.56      inference('demod', [status(thm)], ['13', '16'])).
% 0.19/0.56  thf('18', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.19/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.56  thf('19', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.56  thf(t112_xboole_1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i]:
% 0.19/0.56     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.19/0.56       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.19/0.56  thf('20', plain,
% 0.19/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.56         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 0.19/0.56           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 0.19/0.56      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.19/0.56  thf('21', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 0.19/0.56           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 0.19/0.56      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.56  thf('22', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 0.19/0.56           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.19/0.56      inference('sup+', [status(thm)], ['18', '21'])).
% 0.19/0.56  thf('23', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         ((k4_xboole_0 @ X0 @ X1)
% 0.19/0.56           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.56      inference('sup+', [status(thm)], ['10', '11'])).
% 0.19/0.56  thf('24', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.56  thf('25', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((k4_xboole_0 @ sk_B @ X0)
% 0.19/0.56           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.19/0.56      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.19/0.56  thf('26', plain,
% 0.19/0.56      (((k4_xboole_0 @ sk_B @ sk_B)
% 0.19/0.56         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.56      inference('sup+', [status(thm)], ['17', '25'])).
% 0.19/0.56  thf(t22_xboole_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.19/0.56  thf('27', plain,
% 0.19/0.56      (![X10 : $i, X11 : $i]:
% 0.19/0.56         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.19/0.56      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.19/0.56  thf(t46_xboole_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.19/0.56  thf('28', plain,
% 0.19/0.56      (![X15 : $i, X16 : $i]:
% 0.19/0.56         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 0.19/0.56      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.19/0.56  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.56      inference('sup+', [status(thm)], ['27', '28'])).
% 0.19/0.56  thf('30', plain,
% 0.19/0.56      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.56      inference('demod', [status(thm)], ['26', '29'])).
% 0.19/0.56  thf(t94_xboole_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( k2_xboole_0 @ A @ B ) =
% 0.19/0.56       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.56  thf('31', plain,
% 0.19/0.56      (![X20 : $i, X21 : $i]:
% 0.19/0.56         ((k2_xboole_0 @ X20 @ X21)
% 0.19/0.56           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.19/0.56              (k3_xboole_0 @ X20 @ X21)))),
% 0.19/0.56      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.19/0.56  thf('32', plain,
% 0.19/0.56      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.56         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 0.19/0.56            k1_xboole_0))),
% 0.19/0.56      inference('sup+', [status(thm)], ['30', '31'])).
% 0.19/0.56  thf('33', plain,
% 0.19/0.56      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.56  thf(t48_xboole_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.56  thf('34', plain,
% 0.19/0.56      (![X17 : $i, X18 : $i]:
% 0.19/0.56         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.19/0.56           = (k3_xboole_0 @ X17 @ X18))),
% 0.19/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.56  thf('35', plain,
% 0.19/0.56      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.56         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.56      inference('sup+', [status(thm)], ['33', '34'])).
% 0.19/0.56  thf('36', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.56  thf('37', plain,
% 0.19/0.56      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.56         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.19/0.56  thf('38', plain,
% 0.19/0.56      (![X17 : $i, X18 : $i]:
% 0.19/0.56         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.19/0.56           = (k3_xboole_0 @ X17 @ X18))),
% 0.19/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.56  thf('39', plain,
% 0.19/0.56      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.19/0.56         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.56      inference('sup+', [status(thm)], ['37', '38'])).
% 0.19/0.56  thf('40', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.19/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.56  thf('41', plain,
% 0.19/0.56      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.19/0.56         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.19/0.56  thf('42', plain,
% 0.19/0.56      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.56  thf('43', plain,
% 0.19/0.56      (((k3_subset_1 @ sk_A @ sk_B)
% 0.19/0.56         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.56  thf('44', plain,
% 0.19/0.56      (![X5 : $i, X6 : $i]:
% 0.19/0.56         ((k4_xboole_0 @ X5 @ X6)
% 0.19/0.56           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.19/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.56  thf('45', plain,
% 0.19/0.56      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.56         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.19/0.56  thf('46', plain,
% 0.19/0.56      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.56         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.19/0.56  thf('47', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.19/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.56  thf('48', plain,
% 0.19/0.56      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.19/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.19/0.57  thf('49', plain,
% 0.19/0.57      (((sk_B) = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.57      inference('demod', [status(thm)], ['45', '48'])).
% 0.19/0.57  thf('50', plain,
% 0.19/0.57      (![X20 : $i, X21 : $i]:
% 0.19/0.57         ((k2_xboole_0 @ X20 @ X21)
% 0.19/0.57           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.19/0.57              (k3_xboole_0 @ X20 @ X21)))),
% 0.19/0.57      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.19/0.57  thf('51', plain,
% 0.19/0.57      (((k2_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.57         = (k5_xboole_0 @ sk_B @ 
% 0.19/0.57            (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.19/0.57      inference('sup+', [status(thm)], ['49', '50'])).
% 0.19/0.57  thf('52', plain,
% 0.19/0.57      (((k3_subset_1 @ sk_A @ sk_B)
% 0.19/0.57         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.57  thf('53', plain,
% 0.19/0.57      (![X10 : $i, X11 : $i]:
% 0.19/0.57         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.19/0.57      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.19/0.57  thf('54', plain,
% 0.19/0.57      (((k2_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.19/0.57      inference('sup+', [status(thm)], ['52', '53'])).
% 0.19/0.57  thf('55', plain,
% 0.19/0.57      (((k3_subset_1 @ sk_A @ sk_B)
% 0.19/0.57         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.57  thf('56', plain,
% 0.19/0.57      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.57      inference('demod', [status(thm)], ['51', '54', '55'])).
% 0.19/0.57  thf(t5_boole, axiom,
% 0.19/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.57  thf('57', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.19/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.57  thf('58', plain,
% 0.19/0.57      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.19/0.57      inference('demod', [status(thm)], ['32', '56', '57'])).
% 0.19/0.57  thf('59', plain,
% 0.19/0.57      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.57         != (k2_subset_1 @ sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.57  thf('60', plain, (![X36 : $i]: ((k2_subset_1 @ X36) = (X36))),
% 0.19/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.57  thf('61', plain,
% 0.19/0.57      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.19/0.57      inference('demod', [status(thm)], ['59', '60'])).
% 0.19/0.57  thf('62', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(dt_k3_subset_1, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.57       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.57  thf('63', plain,
% 0.19/0.57      (![X39 : $i, X40 : $i]:
% 0.19/0.57         ((m1_subset_1 @ (k3_subset_1 @ X39 @ X40) @ (k1_zfmisc_1 @ X39))
% 0.19/0.57          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 0.19/0.57      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.19/0.57  thf('64', plain,
% 0.19/0.57      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.57      inference('sup-', [status(thm)], ['62', '63'])).
% 0.19/0.57  thf('65', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(redefinition_k4_subset_1, axiom,
% 0.19/0.57    (![A:$i,B:$i,C:$i]:
% 0.19/0.57     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.19/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.57       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.19/0.57  thf('66', plain,
% 0.19/0.57      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.19/0.57         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.19/0.57          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X43))
% 0.19/0.57          | ((k4_subset_1 @ X43 @ X42 @ X44) = (k2_xboole_0 @ X42 @ X44)))),
% 0.19/0.57      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.19/0.57  thf('67', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.19/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['65', '66'])).
% 0.19/0.57  thf('68', plain,
% 0.19/0.57      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.57         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['64', '67'])).
% 0.19/0.57  thf('69', plain,
% 0.19/0.57      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.19/0.57      inference('demod', [status(thm)], ['61', '68'])).
% 0.19/0.57  thf('70', plain, ($false),
% 0.19/0.57      inference('simplify_reflect-', [status(thm)], ['58', '69'])).
% 0.19/0.57  
% 0.19/0.57  % SZS output end Refutation
% 0.19/0.57  
% 0.19/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
