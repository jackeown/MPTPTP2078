%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bk5dH6ZmcO

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:12 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 136 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  619 (1205 expanded)
%              Number of equality atoms :   36 (  48 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t31_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ C )
            <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k4_xboole_0 @ X15 @ X14 ) @ ( k4_xboole_0 @ X15 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('26',plain,(
    r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ ( k3_tarski @ X23 ) )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('28',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('29',plain,(
    ! [X24: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('30',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['28','29'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['21','36'])).

thf('38',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('47',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ ( k3_tarski @ X23 ) )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('49',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X24: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('51',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('57',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['42','57'])).

thf('59',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('60',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k4_xboole_0 @ X15 @ X14 ) @ ( k4_xboole_0 @ X15 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('61',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['37','62'])).

thf('64',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
   <= ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bk5dH6ZmcO
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:30:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.59/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.76  % Solved by: fo/fo7.sh
% 0.59/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.76  % done 893 iterations in 0.309s
% 0.59/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.76  % SZS output start Refutation
% 0.59/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.76  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.59/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.76  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.59/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.76  thf(t31_subset_1, conjecture,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.76       ( ![C:$i]:
% 0.59/0.76         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.76           ( ( r1_tarski @ B @ C ) <=>
% 0.59/0.76             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.59/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.76    (~( ![A:$i,B:$i]:
% 0.59/0.76        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.76          ( ![C:$i]:
% 0.59/0.76            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.76              ( ( r1_tarski @ B @ C ) <=>
% 0.59/0.76                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.59/0.76    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.59/0.76  thf('0', plain,
% 0.59/0.76      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.59/0.76           (k3_subset_1 @ sk_A @ sk_B))
% 0.59/0.76        | ~ (r1_tarski @ sk_B @ sk_C))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('1', plain,
% 0.59/0.76      (~
% 0.59/0.76       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.59/0.76       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.59/0.76      inference('split', [status(esa)], ['0'])).
% 0.59/0.76  thf('2', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(d5_subset_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.76       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.59/0.76  thf('3', plain,
% 0.59/0.76      (![X28 : $i, X29 : $i]:
% 0.59/0.76         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 0.59/0.76          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.59/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.59/0.76  thf('4', plain,
% 0.59/0.76      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.76  thf('5', plain,
% 0.59/0.76      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))
% 0.59/0.76        | (r1_tarski @ sk_B @ sk_C))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('6', plain,
% 0.59/0.76      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.59/0.76      inference('split', [status(esa)], ['5'])).
% 0.59/0.76  thf(t34_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i]:
% 0.59/0.76     ( ( r1_tarski @ A @ B ) =>
% 0.59/0.76       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.59/0.76  thf('7', plain,
% 0.59/0.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.76         (~ (r1_tarski @ X13 @ X14)
% 0.59/0.76          | (r1_tarski @ (k4_xboole_0 @ X15 @ X14) @ (k4_xboole_0 @ X15 @ X13)))),
% 0.59/0.76      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.59/0.76  thf('8', plain,
% 0.59/0.76      ((![X0 : $i]:
% 0.59/0.76          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.59/0.76         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['6', '7'])).
% 0.59/0.76  thf('9', plain,
% 0.59/0.76      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.59/0.76         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.59/0.76      inference('sup+', [status(thm)], ['4', '8'])).
% 0.59/0.76  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('11', plain,
% 0.59/0.76      (![X28 : $i, X29 : $i]:
% 0.59/0.76         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 0.59/0.76          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.59/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.59/0.76  thf('12', plain,
% 0.59/0.76      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.59/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.76  thf('13', plain,
% 0.59/0.76      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.59/0.76         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.59/0.76      inference('demod', [status(thm)], ['9', '12'])).
% 0.59/0.76  thf('14', plain,
% 0.59/0.76      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.59/0.76           (k3_subset_1 @ sk_A @ sk_B)))
% 0.59/0.76         <= (~
% 0.59/0.76             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.59/0.76               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.59/0.76      inference('split', [status(esa)], ['0'])).
% 0.59/0.76  thf('15', plain,
% 0.59/0.76      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.59/0.76       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('16', plain,
% 0.59/0.76      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.59/0.76       ((r1_tarski @ sk_B @ sk_C))),
% 0.59/0.76      inference('split', [status(esa)], ['5'])).
% 0.59/0.76  thf('17', plain,
% 0.59/0.76      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.76  thf(t48_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.76  thf('18', plain,
% 0.59/0.76      (![X17 : $i, X18 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.76           = (k3_xboole_0 @ X17 @ X18))),
% 0.59/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.76  thf('19', plain,
% 0.59/0.76      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 0.59/0.76         = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.76      inference('sup+', [status(thm)], ['17', '18'])).
% 0.59/0.76  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.76  thf('20', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.76  thf('21', plain,
% 0.59/0.76      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 0.59/0.76         = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.59/0.76      inference('demod', [status(thm)], ['19', '20'])).
% 0.59/0.76  thf('22', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(d2_subset_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( ( v1_xboole_0 @ A ) =>
% 0.59/0.76         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.59/0.76       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.76         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.76  thf('23', plain,
% 0.59/0.76      (![X25 : $i, X26 : $i]:
% 0.59/0.76         (~ (m1_subset_1 @ X25 @ X26)
% 0.59/0.76          | (r2_hidden @ X25 @ X26)
% 0.59/0.76          | (v1_xboole_0 @ X26))),
% 0.59/0.76      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.76  thf('24', plain,
% 0.59/0.76      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.59/0.76        | (r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.59/0.76  thf(fc1_subset_1, axiom,
% 0.59/0.76    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.59/0.76  thf('25', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.59/0.76      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.59/0.76  thf('26', plain, ((r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.76      inference('clc', [status(thm)], ['24', '25'])).
% 0.59/0.76  thf(l49_zfmisc_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.59/0.76  thf('27', plain,
% 0.59/0.76      (![X22 : $i, X23 : $i]:
% 0.59/0.76         ((r1_tarski @ X22 @ (k3_tarski @ X23)) | ~ (r2_hidden @ X22 @ X23))),
% 0.59/0.76      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.59/0.76  thf('28', plain, ((r1_tarski @ sk_C @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['26', '27'])).
% 0.59/0.76  thf(t99_zfmisc_1, axiom,
% 0.59/0.76    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.59/0.76  thf('29', plain, (![X24 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X24)) = (X24))),
% 0.59/0.76      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.59/0.76  thf('30', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.59/0.76      inference('demod', [status(thm)], ['28', '29'])).
% 0.59/0.76  thf(l32_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.76  thf('31', plain,
% 0.59/0.76      (![X4 : $i, X6 : $i]:
% 0.59/0.76         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.59/0.76      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.76  thf('32', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.59/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.76  thf('33', plain,
% 0.59/0.76      (![X17 : $i, X18 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.76           = (k3_xboole_0 @ X17 @ X18))),
% 0.59/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.76  thf('34', plain,
% 0.59/0.76      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.59/0.76      inference('sup+', [status(thm)], ['32', '33'])).
% 0.59/0.76  thf(t3_boole, axiom,
% 0.59/0.76    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.76  thf('35', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.59/0.76      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.76  thf('36', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.59/0.76      inference('demod', [status(thm)], ['34', '35'])).
% 0.59/0.76  thf('37', plain,
% 0.59/0.76      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['21', '36'])).
% 0.59/0.76  thf('38', plain,
% 0.59/0.76      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.59/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.76  thf('39', plain,
% 0.59/0.76      (![X17 : $i, X18 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.76           = (k3_xboole_0 @ X17 @ X18))),
% 0.59/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.76  thf('40', plain,
% 0.59/0.76      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.59/0.76         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['38', '39'])).
% 0.59/0.76  thf('41', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.76  thf('42', plain,
% 0.59/0.76      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.59/0.76         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.59/0.76      inference('demod', [status(thm)], ['40', '41'])).
% 0.59/0.76  thf('43', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('44', plain,
% 0.59/0.76      (![X25 : $i, X26 : $i]:
% 0.59/0.76         (~ (m1_subset_1 @ X25 @ X26)
% 0.59/0.76          | (r2_hidden @ X25 @ X26)
% 0.59/0.76          | (v1_xboole_0 @ X26))),
% 0.59/0.76      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.76  thf('45', plain,
% 0.59/0.76      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.59/0.76        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['43', '44'])).
% 0.59/0.76  thf('46', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.59/0.76      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.59/0.76  thf('47', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.76      inference('clc', [status(thm)], ['45', '46'])).
% 0.59/0.76  thf('48', plain,
% 0.59/0.76      (![X22 : $i, X23 : $i]:
% 0.59/0.76         ((r1_tarski @ X22 @ (k3_tarski @ X23)) | ~ (r2_hidden @ X22 @ X23))),
% 0.59/0.76      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.59/0.76  thf('49', plain, ((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['47', '48'])).
% 0.59/0.76  thf('50', plain, (![X24 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X24)) = (X24))),
% 0.59/0.76      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.59/0.76  thf('51', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.59/0.76      inference('demod', [status(thm)], ['49', '50'])).
% 0.59/0.76  thf('52', plain,
% 0.59/0.76      (![X4 : $i, X6 : $i]:
% 0.59/0.76         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.59/0.76      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.76  thf('53', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.59/0.76      inference('sup-', [status(thm)], ['51', '52'])).
% 0.59/0.76  thf('54', plain,
% 0.59/0.76      (![X17 : $i, X18 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.76           = (k3_xboole_0 @ X17 @ X18))),
% 0.59/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.76  thf('55', plain,
% 0.59/0.76      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.59/0.76      inference('sup+', [status(thm)], ['53', '54'])).
% 0.59/0.76  thf('56', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.59/0.76      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.76  thf('57', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.59/0.76      inference('demod', [status(thm)], ['55', '56'])).
% 0.59/0.76  thf('58', plain,
% 0.59/0.76      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.59/0.76      inference('demod', [status(thm)], ['42', '57'])).
% 0.59/0.76  thf('59', plain,
% 0.59/0.76      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.59/0.76         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.59/0.76               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.59/0.76      inference('split', [status(esa)], ['5'])).
% 0.59/0.76  thf('60', plain,
% 0.59/0.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.76         (~ (r1_tarski @ X13 @ X14)
% 0.59/0.76          | (r1_tarski @ (k4_xboole_0 @ X15 @ X14) @ (k4_xboole_0 @ X15 @ X13)))),
% 0.59/0.76      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.59/0.76  thf('61', plain,
% 0.59/0.76      ((![X0 : $i]:
% 0.59/0.76          (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 0.59/0.76           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C))))
% 0.59/0.76         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.59/0.76               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.59/0.76      inference('sup-', [status(thm)], ['59', '60'])).
% 0.59/0.76  thf('62', plain,
% 0.59/0.76      (((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))))
% 0.59/0.76         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.59/0.76               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.59/0.76      inference('sup+', [status(thm)], ['58', '61'])).
% 0.59/0.76  thf('63', plain,
% 0.59/0.76      (((r1_tarski @ sk_B @ sk_C))
% 0.59/0.76         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.59/0.76               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.59/0.76      inference('sup+', [status(thm)], ['37', '62'])).
% 0.59/0.76  thf('64', plain,
% 0.59/0.76      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 0.59/0.76      inference('split', [status(esa)], ['0'])).
% 0.59/0.76  thf('65', plain,
% 0.59/0.76      (~
% 0.59/0.76       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.59/0.76       ((r1_tarski @ sk_B @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['63', '64'])).
% 0.59/0.76  thf('66', plain, ($false),
% 0.59/0.76      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '65'])).
% 0.59/0.76  
% 0.59/0.76  % SZS output end Refutation
% 0.59/0.76  
% 0.59/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
