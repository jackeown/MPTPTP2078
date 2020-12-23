%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s74wmAfpMo

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:19 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 161 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  852 (2278 expanded)
%              Number of equality atoms :   35 (  89 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t86_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( r1_tarski @ C @ B )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r1_tarski @ C @ B )
                      & ( v3_pre_topc @ C @ A ) )
                   => ( C = k1_xboole_0 ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tops_1])).

thf('0',plain,(
    ! [X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X24 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X24 @ sk_A )
      | ~ ( r1_tarski @ X24 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X15 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('20',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k1_tops_1 @ X23 @ X22 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ~ ! [X24: $i] :
          ( ( X24 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X24 @ sk_A )
          | ~ ( r1_tarski @ X24 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('36',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tops_1 @ X22 @ X23 )
      | ( ( k1_tops_1 @ X23 @ X22 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['32'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['40'])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( r1_tarski @ X19 @ ( k1_tops_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_C @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['48','59'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('62',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('68',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','34','35','37','39','41','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s74wmAfpMo
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:18:19 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  % Running portfolio for 600 s
% 0.18/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.34  % Number of cores: 8
% 0.18/0.34  % Python version: Python 3.6.8
% 0.18/0.34  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 672 iterations in 0.191s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.63  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(t86_tops_1, conjecture,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( ( v2_tops_1 @ B @ A ) <=>
% 0.46/0.63             ( ![C:$i]:
% 0.46/0.63               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.46/0.63                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]:
% 0.46/0.63        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63          ( ![B:$i]:
% 0.46/0.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63              ( ( v2_tops_1 @ B @ A ) <=>
% 0.46/0.63                ( ![C:$i]:
% 0.46/0.63                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.46/0.63                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      (![X24 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63          | ((X24) = (k1_xboole_0))
% 0.46/0.63          | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.46/0.63          | ~ (r1_tarski @ X24 @ sk_B)
% 0.46/0.63          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      ((![X24 : $i]:
% 0.46/0.63          (((X24) = (k1_xboole_0))
% 0.46/0.63           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.46/0.63           | ~ (r1_tarski @ X24 @ sk_B))) | 
% 0.46/0.63       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('split', [status(esa)], ['0'])).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t3_subset, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i]:
% 0.46/0.63         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.63  thf('4', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t44_tops_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      (![X17 : $i, X18 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.63          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ X17)
% 0.46/0.63          | ~ (l1_pre_topc @ X18))),
% 0.46/0.63      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.63  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('9', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.46/0.63      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.63  thf(t1_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.63       ( r1_tarski @ A @ C ) ))).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.63         (~ (r1_tarski @ X5 @ X6)
% 0.46/0.63          | ~ (r1_tarski @ X6 @ X7)
% 0.46/0.63          | (r1_tarski @ X5 @ X7))),
% 0.46/0.63      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.46/0.63          | ~ (r1_tarski @ sk_B @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['4', '11'])).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      (![X12 : $i, X14 : $i]:
% 0.46/0.63         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.46/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      ((![X24 : $i]:
% 0.46/0.63          (((X24) = (k1_xboole_0))
% 0.46/0.63           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.46/0.63           | ~ (r1_tarski @ X24 @ sk_B)))
% 0.46/0.63         <= ((![X24 : $i]:
% 0.46/0.63                (((X24) = (k1_xboole_0))
% 0.46/0.63                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.46/0.63                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.46/0.63      inference('split', [status(esa)], ['0'])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.46/0.63         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.46/0.63         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.46/0.63         <= ((![X24 : $i]:
% 0.46/0.63                (((X24) = (k1_xboole_0))
% 0.46/0.63                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.46/0.63                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.63  thf('17', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.46/0.63      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(fc9_tops_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.46/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (![X15 : $i, X16 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X15)
% 0.46/0.63          | ~ (v2_pre_topc @ X15)
% 0.46/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.63          | (v3_pre_topc @ (k1_tops_1 @ X15 @ X16) @ X15))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.46/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.63  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('23', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.46/0.63         <= ((![X24 : $i]:
% 0.46/0.63                (((X24) = (k1_xboole_0))
% 0.46/0.63                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.46/0.63                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.46/0.63      inference('demod', [status(thm)], ['16', '17', '23'])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t84_tops_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( ( v2_tops_1 @ B @ A ) <=>
% 0.46/0.63             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (![X22 : $i, X23 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.46/0.63          | ((k1_tops_1 @ X23 @ X22) != (k1_xboole_0))
% 0.46/0.63          | (v2_tops_1 @ X22 @ X23)
% 0.46/0.63          | ~ (l1_pre_topc @ X23))),
% 0.46/0.63      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | (v2_tops_1 @ sk_B @ sk_A)
% 0.46/0.63        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.63  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      (((v2_tops_1 @ sk_B @ sk_A)
% 0.46/0.63        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.63  thf('30', plain,
% 0.46/0.63      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.46/0.63         <= ((![X24 : $i]:
% 0.46/0.63                (((X24) = (k1_xboole_0))
% 0.46/0.63                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.46/0.63                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['24', '29'])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      (((v2_tops_1 @ sk_B @ sk_A))
% 0.46/0.63         <= ((![X24 : $i]:
% 0.46/0.63                (((X24) = (k1_xboole_0))
% 0.46/0.63                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.46/0.63                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.46/0.63      inference('simplify', [status(thm)], ['30'])).
% 0.46/0.63  thf('32', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('split', [status(esa)], ['32'])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      (~
% 0.46/0.63       (![X24 : $i]:
% 0.46/0.63          (((X24) = (k1_xboole_0))
% 0.46/0.63           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.46/0.63           | ~ (r1_tarski @ X24 @ sk_B))) | 
% 0.46/0.63       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['31', '33'])).
% 0.46/0.63  thf('35', plain,
% 0.46/0.63      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('split', [status(esa)], ['32'])).
% 0.46/0.63  thf('36', plain,
% 0.46/0.63      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('split', [status(esa)], ['36'])).
% 0.46/0.63  thf('38', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('split', [status(esa)], ['38'])).
% 0.46/0.63  thf('40', plain,
% 0.46/0.63      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('41', plain,
% 0.46/0.63      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.46/0.63       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('split', [status(esa)], ['40'])).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('split', [status(esa)], ['0'])).
% 0.46/0.63  thf('43', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      (![X22 : $i, X23 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.46/0.63          | ~ (v2_tops_1 @ X22 @ X23)
% 0.46/0.63          | ((k1_tops_1 @ X23 @ X22) = (k1_xboole_0))
% 0.46/0.63          | ~ (l1_pre_topc @ X23))),
% 0.46/0.63      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.46/0.63  thf('45', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.63        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.63  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('47', plain,
% 0.46/0.63      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.63        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.46/0.63         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['42', '47'])).
% 0.46/0.63  thf('49', plain,
% 0.46/0.63      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.46/0.63      inference('split', [status(esa)], ['32'])).
% 0.46/0.63  thf('50', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.46/0.63      inference('split', [status(esa)], ['36'])).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.63         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('split', [status(esa)], ['40'])).
% 0.46/0.63  thf(t56_tops_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.63                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('53', plain,
% 0.46/0.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.63          | ~ (v3_pre_topc @ X19 @ X20)
% 0.46/0.63          | ~ (r1_tarski @ X19 @ X21)
% 0.46/0.63          | (r1_tarski @ X19 @ (k1_tops_1 @ X20 @ X21))
% 0.46/0.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.63          | ~ (l1_pre_topc @ X20))),
% 0.46/0.63      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.46/0.63  thf('54', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          (~ (l1_pre_topc @ sk_A)
% 0.46/0.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.46/0.63           | ~ (r1_tarski @ sk_C @ X0)
% 0.46/0.63           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.46/0.63         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.63  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('56', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.46/0.63           | ~ (r1_tarski @ sk_C @ X0)
% 0.46/0.63           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.46/0.63         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.63  thf('57', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          (~ (r1_tarski @ sk_C @ X0)
% 0.46/0.63           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.46/0.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.63         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.46/0.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['51', '56'])).
% 0.46/0.63  thf('58', plain,
% 0.46/0.63      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))
% 0.46/0.63         | ~ (r1_tarski @ sk_C @ sk_B)))
% 0.46/0.63         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.46/0.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['50', '57'])).
% 0.46/0.63  thf('59', plain,
% 0.46/0.63      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.46/0.63         <= (((r1_tarski @ sk_C @ sk_B)) & 
% 0.46/0.63             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.46/0.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['49', '58'])).
% 0.46/0.63  thf('60', plain,
% 0.46/0.63      (((r1_tarski @ sk_C @ k1_xboole_0))
% 0.46/0.63         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.46/0.63             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.46/0.63             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.46/0.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup+', [status(thm)], ['48', '59'])).
% 0.46/0.63  thf(t46_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.46/0.63  thf('61', plain,
% 0.46/0.63      (![X10 : $i, X11 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.46/0.63  thf(t36_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.63  thf('62', plain,
% 0.46/0.63      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.46/0.63      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.46/0.63  thf('63', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.63      inference('sup+', [status(thm)], ['61', '62'])).
% 0.46/0.63  thf(d10_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.63  thf('64', plain,
% 0.46/0.63      (![X0 : $i, X2 : $i]:
% 0.46/0.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.63  thf('65', plain,
% 0.46/0.63      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['63', '64'])).
% 0.46/0.63  thf('66', plain,
% 0.46/0.63      ((((sk_C) = (k1_xboole_0)))
% 0.46/0.63         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.46/0.63             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.46/0.63             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.46/0.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['60', '65'])).
% 0.46/0.63  thf('67', plain,
% 0.46/0.63      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.46/0.63      inference('split', [status(esa)], ['38'])).
% 0.46/0.63  thf('68', plain,
% 0.46/0.63      ((((sk_C) != (sk_C)))
% 0.46/0.63         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.46/0.63             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.46/0.63             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.46/0.63             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.46/0.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['66', '67'])).
% 0.46/0.63  thf('69', plain,
% 0.46/0.63      (~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.46/0.63       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.46/0.63       ~ ((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.46/0.63       (((sk_C) = (k1_xboole_0)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['68'])).
% 0.46/0.63  thf('70', plain, ($false),
% 0.46/0.63      inference('sat_resolution*', [status(thm)],
% 0.46/0.63                ['1', '34', '35', '37', '39', '41', '69'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
