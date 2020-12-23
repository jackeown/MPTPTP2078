%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zHtonZ3vos

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 226 expanded)
%              Number of leaves         :   24 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          :  685 (1756 expanded)
%              Number of equality atoms :   84 ( 195 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X34 @ ( k3_subset_1 @ X34 @ X33 ) )
        = X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('9',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k3_subset_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('16',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('17',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('18',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('21',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('30',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['15','28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['13','30'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('38',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['41','42'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('44',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','58'])).

thf('60',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['19','20'])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','59','60'])).

thf('62',plain,
    ( ( k3_subset_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['2','61'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('63',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X29 ) @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('64',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('65',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X34 @ ( k3_subset_1 @ X34 @ X33 ) )
        = X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('69',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('70',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['62','73'])).

thf('75',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('76',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('77',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['15','28'])).

thf('79',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['74','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zHtonZ3vos
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:22:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 173 iterations in 0.048s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(t39_subset_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.21/0.50         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.21/0.50            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.21/0.50  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X33 : $i, X34 : $i]:
% 0.21/0.50         (((k3_subset_1 @ X34 @ (k3_subset_1 @ X34 @ X33)) = (X33))
% 0.21/0.50          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.21/0.50      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d5_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X27 : $i, X28 : $i]:
% 0.21/0.50         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.21/0.50          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf(t48_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.21/0.50           = (k3_xboole_0 @ X21 @ X22))),
% 0.21/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.50         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf(t38_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.21/0.50       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i]:
% 0.21/0.50         (((X15) = (k1_xboole_0))
% 0.21/0.50          | ~ (r1_tarski @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.21/0.50           (k3_xboole_0 @ sk_A @ sk_B))
% 0.21/0.50        | ((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.21/0.50        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.21/0.50         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['10'])).
% 0.21/0.50  thf(l32_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X5 : $i, X7 : $i]:
% 0.21/0.50         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.21/0.50         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.21/0.50        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.21/0.50       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.50      inference('split', [status(esa)], ['14'])).
% 0.21/0.50  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.50  thf('16', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('split', [status(esa)], ['10'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf(t36_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.21/0.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.50  thf('21', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.21/0.50         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['18', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.21/0.50         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['14'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.21/0.50         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.21/0.50             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.21/0.50         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.21/0.50             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.21/0.50       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.21/0.50       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['10'])).
% 0.21/0.50  thf('30', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['15', '28', '29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['13', '30'])).
% 0.21/0.50  thf(t39_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.21/0.50           = (k2_xboole_0 @ X17 @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.21/0.50         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (((k2_xboole_0 @ k1_xboole_0 @ sk_B)
% 0.21/0.50         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.21/0.50           = (k2_xboole_0 @ X17 @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.50         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.50         = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (((k2_xboole_0 @ k1_xboole_0 @ sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup+', [status(thm)], ['35', '40'])).
% 0.21/0.50  thf(t21_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ k1_xboole_0 @ sk_B)) = (sk_A))),
% 0.21/0.50      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.50  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.50  thf('44', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.51  thf('46', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.21/0.51           = (k3_xboole_0 @ X21 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.21/0.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.21/0.51      inference('sup+', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['46', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X5 : $i, X7 : $i]:
% 0.21/0.51         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.51  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.21/0.51           = (k2_xboole_0 @ X17 @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('55', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.51  thf('56', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.51  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['56', '57'])).
% 0.21/0.51  thf('59', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['43', '58'])).
% 0.21/0.51  thf('60', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.51      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('61', plain, (((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['9', '59', '60'])).
% 0.21/0.51  thf('62', plain, (((k3_subset_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['2', '61'])).
% 0.21/0.51  thf(dt_k2_subset_1, axiom,
% 0.21/0.51    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (![X29 : $i]: (m1_subset_1 @ (k2_subset_1 @ X29) @ (k1_zfmisc_1 @ X29))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.51  thf('64', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.51  thf('65', plain, (![X29 : $i]: (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X29))),
% 0.21/0.51      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (![X33 : $i, X34 : $i]:
% 0.21/0.51         (((k3_subset_1 @ X34 @ (k3_subset_1 @ X34 @ X33)) = (X33))
% 0.21/0.51          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.21/0.51      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.51  thf('68', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.51  thf('69', plain, (![X29 : $i]: (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X29))),
% 0.21/0.51      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (![X27 : $i, X28 : $i]:
% 0.21/0.51         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.21/0.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.51  thf('72', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['68', '71'])).
% 0.21/0.51  thf('73', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['67', '72'])).
% 0.21/0.51  thf('74', plain, (((sk_A) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['62', '73'])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.21/0.51         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.51      inference('split', [status(esa)], ['14'])).
% 0.21/0.51  thf('76', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['75', '76'])).
% 0.21/0.51  thf('78', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['15', '28'])).
% 0.21/0.51  thf('79', plain, (((sk_B) != (sk_A))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['77', '78'])).
% 0.21/0.51  thf('80', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['74', '79'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
