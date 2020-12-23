%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gJw0swiv66

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:40 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 128 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  602 (1882 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(t20_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v8_pre_topc @ A )
                  & ( v2_compts_1 @ B @ A )
                  & ( v2_compts_1 @ C @ A ) )
               => ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v8_pre_topc @ A )
                    & ( v2_compts_1 @ B @ A )
                    & ( v2_compts_1 @ C @ A ) )
                 => ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_compts_1])).

thf('0',plain,(
    ~ ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_pre_topc @ X15 @ X16 )
      | ~ ( v4_pre_topc @ X17 @ X16 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ X17 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v8_pre_topc @ A )
              & ( v2_compts_1 @ B @ A ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( v2_compts_1 @ X18 @ X19 )
      | ~ ( v8_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('14',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','19'])).

thf('21',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( v2_compts_1 @ X18 @ X19 )
      | ~ ( v8_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('24',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('31',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['21','29','30'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_compts_1 @ B @ A )
                  & ( r1_tarski @ C @ B )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v2_compts_1 @ C @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_compts_1 @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ~ ( v4_pre_topc @ X22 @ X21 )
      | ( v2_compts_1 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_compts_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['31','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['4','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gJw0swiv66
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:37:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 214 iterations in 0.164s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.39/0.62  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.39/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.62  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.39/0.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.39/0.62  thf(t20_compts_1, conjecture,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.62           ( ![C:$i]:
% 0.39/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.62               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.39/0.62                   ( v2_compts_1 @ C @ A ) ) =>
% 0.39/0.62                 ( v2_compts_1 @
% 0.39/0.62                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i]:
% 0.39/0.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.62          ( ![B:$i]:
% 0.39/0.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.62              ( ![C:$i]:
% 0.39/0.62                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.62                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.39/0.62                      ( v2_compts_1 @ C @ A ) ) =>
% 0.39/0.62                    ( v2_compts_1 @
% 0.39/0.62                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.39/0.62  thf('0', plain,
% 0.39/0.62      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.39/0.62          sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(redefinition_k9_subset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.62       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.62         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.39/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.39/0.62           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.62  thf('4', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.39/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t35_tops_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.62           ( ![C:$i]:
% 0.39/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.62               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.39/0.62                 ( v4_pre_topc @
% 0.39/0.62                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.39/0.62          | ~ (v4_pre_topc @ X15 @ X16)
% 0.39/0.62          | ~ (v4_pre_topc @ X17 @ X16)
% 0.39/0.62          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ X16) @ X15 @ X17) @ 
% 0.39/0.62             X16)
% 0.39/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.39/0.62          | ~ (l1_pre_topc @ X16)
% 0.39/0.62          | ~ (v2_pre_topc @ X16))),
% 0.39/0.62      inference('cnf', [status(esa)], [t35_tops_1])).
% 0.39/0.62  thf('8', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v2_pre_topc @ sk_A)
% 0.39/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.62          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.39/0.62             sk_A)
% 0.39/0.62          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.39/0.62          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.62  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.62          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.39/0.62             sk_A)
% 0.39/0.62          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.39/0.62          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t16_compts_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.62           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.39/0.62             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.39/0.62  thf('13', plain,
% 0.39/0.62      (![X18 : $i, X19 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.39/0.62          | (v4_pre_topc @ X18 @ X19)
% 0.39/0.62          | ~ (v2_compts_1 @ X18 @ X19)
% 0.39/0.62          | ~ (v8_pre_topc @ X19)
% 0.39/0.62          | ~ (l1_pre_topc @ X19)
% 0.39/0.62          | ~ (v2_pre_topc @ X19))),
% 0.39/0.62      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.39/0.62  thf('14', plain,
% 0.39/0.62      ((~ (v2_pre_topc @ sk_A)
% 0.39/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.62        | ~ (v8_pre_topc @ sk_A)
% 0.39/0.62        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.39/0.62        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.62  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('17', plain, ((v8_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('18', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('19', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.39/0.62      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.62          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.39/0.62             sk_A)
% 0.39/0.62          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['11', '19'])).
% 0.39/0.62  thf('21', plain,
% 0.39/0.62      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.39/0.62        | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.39/0.62           sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['5', '20'])).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('23', plain,
% 0.39/0.62      (![X18 : $i, X19 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.39/0.62          | (v4_pre_topc @ X18 @ X19)
% 0.39/0.62          | ~ (v2_compts_1 @ X18 @ X19)
% 0.39/0.62          | ~ (v8_pre_topc @ X19)
% 0.39/0.62          | ~ (l1_pre_topc @ X19)
% 0.39/0.62          | ~ (v2_pre_topc @ X19))),
% 0.39/0.62      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.39/0.62  thf('24', plain,
% 0.39/0.62      ((~ (v2_pre_topc @ sk_A)
% 0.39/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.62        | ~ (v8_pre_topc @ sk_A)
% 0.39/0.62        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.39/0.62        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.62  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('27', plain, ((v8_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('28', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('29', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.39/0.62      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.39/0.62  thf('30', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.39/0.62           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.62  thf('31', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.39/0.62      inference('demod', [status(thm)], ['21', '29', '30'])).
% 0.39/0.62  thf(t48_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.39/0.62           = (k3_xboole_0 @ X5 @ X6))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf('33', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t3_subset, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      (![X12 : $i, X13 : $i]:
% 0.39/0.62         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('35', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.62  thf(t109_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.39/0.62  thf('36', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.62  thf('38', plain,
% 0.39/0.62      (![X12 : $i, X14 : $i]:
% 0.39/0.62         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('39', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.39/0.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.62  thf('40', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.39/0.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['32', '39'])).
% 0.39/0.62  thf('41', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t18_compts_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.62           ( ![C:$i]:
% 0.39/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.62               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.39/0.62                   ( v4_pre_topc @ C @ A ) ) =>
% 0.39/0.62                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.39/0.62  thf('42', plain,
% 0.39/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.39/0.62          | ~ (v2_compts_1 @ X20 @ X21)
% 0.39/0.62          | ~ (r1_tarski @ X22 @ X20)
% 0.39/0.62          | ~ (v4_pre_topc @ X22 @ X21)
% 0.39/0.62          | (v2_compts_1 @ X22 @ X21)
% 0.39/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.39/0.62          | ~ (l1_pre_topc @ X21)
% 0.39/0.62          | ~ (v2_pre_topc @ X21))),
% 0.39/0.62      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.39/0.62  thf('43', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v2_pre_topc @ sk_A)
% 0.39/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.62          | (v2_compts_1 @ X0 @ sk_A)
% 0.39/0.62          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.39/0.62          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.62          | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.62  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('46', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.62          | (v2_compts_1 @ X0 @ sk_A)
% 0.39/0.62          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.39/0.62          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.39/0.62  thf('48', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.39/0.62          | ~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.39/0.62          | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['40', '47'])).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.39/0.62           = (k3_xboole_0 @ X5 @ X6))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf(t36_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.62  thf('50', plain,
% 0.39/0.62      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.39/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.39/0.62      inference('sup+', [status(thm)], ['49', '50'])).
% 0.39/0.62  thf('52', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.39/0.62          | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['48', '51'])).
% 0.39/0.62  thf('53', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.39/0.62      inference('sup-', [status(thm)], ['31', '52'])).
% 0.39/0.62  thf('54', plain, ($false), inference('demod', [status(thm)], ['4', '53'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
