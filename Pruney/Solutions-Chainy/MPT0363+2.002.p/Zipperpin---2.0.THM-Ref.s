%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GvOAbCdkAL

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 168 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  626 (1570 expanded)
%              Number of equality atoms :   32 (  48 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t43_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ C )
            <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k4_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('8',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['6','14'])).

thf('16',plain,(
    ~ ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['5','15'])).

thf('17',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('18',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['8'])).

thf('19',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['6','14','18'])).

thf('20',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['17','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X21 @ ( k3_subset_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('28',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('30',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k4_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('32',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['25','34'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_A ),
    inference('sup+',[status(thm)],['35','36'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X21 @ ( k3_subset_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('45',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k4_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('48',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('52',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('54',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k4_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('56',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['49','58'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('60',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('61',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k2_xboole_0 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('62',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['42','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['16','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GvOAbCdkAL
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:46:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 191 iterations in 0.059s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(t43_subset_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53       ( ![C:$i]:
% 0.22/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.22/0.53             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i]:
% 0.22/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53          ( ![C:$i]:
% 0.22/0.53            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53              ( ( r1_xboole_0 @ B @ C ) <=>
% 0.22/0.53                ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t43_subset_1])).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.22/0.53        | ~ (r1_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.22/0.53         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.22/0.53      inference('split', [status(esa)], ['0'])).
% 0.22/0.53  thf('2', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(d5_subset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i]:
% 0.22/0.53         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 0.22/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      ((~ (r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))
% 0.22/0.53         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.22/0.53      inference('demod', [status(thm)], ['1', '4'])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.22/0.53       ~ ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.53      inference('split', [status(esa)], ['0'])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.22/0.53        | (r1_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.22/0.53         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.22/0.53      inference('split', [status(esa)], ['8'])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))
% 0.22/0.53         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['7', '9'])).
% 0.22/0.53  thf(t106_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.22/0.53       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ X2 @ X4)
% 0.22/0.53          | ~ (r1_tarski @ X2 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (((r1_xboole_0 @ sk_B @ sk_C))
% 0.22/0.53         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      ((~ (r1_xboole_0 @ sk_B @ sk_C)) <= (~ ((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.53      inference('split', [status(esa)], ['0'])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (((r1_xboole_0 @ sk_B @ sk_C)) | 
% 0.22/0.53       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.53  thf('15', plain, (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['6', '14'])).
% 0.22/0.53  thf('16', plain, (~ (r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['5', '15'])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (((r1_xboole_0 @ sk_B @ sk_C)) <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.53      inference('split', [status(esa)], ['8'])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (((r1_xboole_0 @ sk_B @ sk_C)) | 
% 0.22/0.53       ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.22/0.53      inference('split', [status(esa)], ['8'])).
% 0.22/0.53  thf('19', plain, (((r1_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['6', '14', '18'])).
% 0.22/0.53  thf('20', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['17', '19'])).
% 0.22/0.53  thf('21', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X20 : $i, X21 : $i]:
% 0.22/0.53         (((k3_subset_1 @ X21 @ (k3_subset_1 @ X21 @ X20)) = (X20))
% 0.22/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.22/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.22/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_C))),
% 0.22/0.53      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.53  thf('26', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(dt_k3_subset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      (![X18 : $i, X19 : $i]:
% 0.22/0.53         ((m1_subset_1 @ (k3_subset_1 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 0.22/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i]:
% 0.22/0.53         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 0.22/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.22/0.53         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.53  thf(t48_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      (![X8 : $i, X9 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.22/0.53           = (k3_xboole_0 @ X8 @ X9))),
% 0.22/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.22/0.53         = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.53  thf('35', plain, (((sk_C) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.53      inference('sup+', [status(thm)], ['25', '34'])).
% 0.22/0.53  thf(t51_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.22/0.53       ( A ) ))).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      (![X10 : $i, X11 : $i]:
% 0.22/0.53         ((k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k4_xboole_0 @ X10 @ X11))
% 0.22/0.53           = (X10))),
% 0.22/0.53      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.22/0.53  thf('37', plain,
% 0.22/0.53      (((k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_A))),
% 0.22/0.53      inference('sup+', [status(thm)], ['35', '36'])).
% 0.22/0.53  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.53  thf(t73_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.22/0.53       ( r1_tarski @ A @ B ) ))).
% 0.22/0.53  thf('39', plain,
% 0.22/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.53         ((r1_tarski @ X13 @ X14)
% 0.22/0.53          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 0.22/0.53          | ~ (r1_xboole_0 @ X13 @ X15))),
% 0.22/0.53      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.22/0.53  thf('40', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.22/0.53          | ~ (r1_xboole_0 @ X2 @ X1)
% 0.22/0.53          | (r1_tarski @ X2 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.53  thf('41', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (r1_tarski @ X0 @ sk_A)
% 0.22/0.53          | (r1_tarski @ X0 @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.22/0.53          | ~ (r1_xboole_0 @ X0 @ sk_C))),
% 0.22/0.53      inference('sup-', [status(thm)], ['37', '40'])).
% 0.22/0.53  thf('42', plain,
% 0.22/0.53      (((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.22/0.53        | ~ (r1_tarski @ sk_B @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['20', '41'])).
% 0.22/0.53  thf('43', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('44', plain,
% 0.22/0.53      (![X20 : $i, X21 : $i]:
% 0.22/0.53         (((k3_subset_1 @ X21 @ (k3_subset_1 @ X21 @ X20)) = (X20))
% 0.22/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.22/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.53  thf('45', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.53  thf('46', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('47', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i]:
% 0.22/0.53         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 0.22/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.53  thf('48', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.53  thf('49', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['45', '48'])).
% 0.22/0.53  thf('50', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('51', plain,
% 0.22/0.53      (![X18 : $i, X19 : $i]:
% 0.22/0.53         ((m1_subset_1 @ (k3_subset_1 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 0.22/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.53  thf('52', plain,
% 0.22/0.53      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.53  thf('53', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.53  thf('54', plain,
% 0.22/0.53      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['52', '53'])).
% 0.22/0.53  thf('55', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i]:
% 0.22/0.53         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 0.22/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.53  thf('56', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.22/0.53         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.53  thf('57', plain,
% 0.22/0.53      (![X8 : $i, X9 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.22/0.53           = (k3_xboole_0 @ X8 @ X9))),
% 0.22/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.53  thf('58', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.22/0.53         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['56', '57'])).
% 0.22/0.53  thf('59', plain, (((sk_B) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.53      inference('sup+', [status(thm)], ['49', '58'])).
% 0.22/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.53  thf('60', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.22/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.53  thf(t29_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 0.22/0.53  thf('61', plain,
% 0.22/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.53         (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ (k2_xboole_0 @ X5 @ X7))),
% 0.22/0.53      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.22/0.53  thf('62', plain,
% 0.22/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.53         ((r1_tarski @ X13 @ X14)
% 0.22/0.53          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 0.22/0.53          | ~ (r1_xboole_0 @ X13 @ X15))),
% 0.22/0.53      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.22/0.53  thf('63', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ X0)
% 0.22/0.53          | (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.53  thf('64', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.22/0.53      inference('sup-', [status(thm)], ['60', '63'])).
% 0.22/0.53  thf('65', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.53      inference('sup+', [status(thm)], ['59', '64'])).
% 0.22/0.53  thf('66', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.53      inference('demod', [status(thm)], ['42', '65'])).
% 0.22/0.53  thf('67', plain, ($false), inference('demod', [status(thm)], ['16', '66'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
