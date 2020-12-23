%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oJzAtsSUsT

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:58 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 661 expanded)
%              Number of leaves         :   24 ( 179 expanded)
%              Depth                    :   31
%              Number of atoms          : 1837 (12738 expanded)
%              Number of equality atoms :   25 ( 116 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(t9_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( m1_connsp_2 @ D @ A @ C )
                            & ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ~ ( ( r2_hidden @ C @ B )
                      & ! [D: $i] :
                          ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( ( m1_connsp_2 @ D @ A @ C )
                              & ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_connsp_2])).

thf('0',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X23 @ sk_A @ sk_C_1 )
      | ~ ( r1_tarski @ X23 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X23 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X23 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X22 @ sk_B )
      | ( r1_tarski @ ( sk_D @ X22 ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X15 )
      | ( ( k1_tops_1 @ X15 @ X16 )
        = X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('14',plain,
    ( ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
        | ~ ( v3_pre_topc @ X16 @ X15 )
        | ( ( k1_tops_1 @ X15 @ X16 )
          = X16 ) )
   <= ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
        | ~ ( v3_pre_topc @ X16 @ X15 )
        | ( ( k1_tops_1 @ X15 @ X16 )
          = X16 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 ) )
   <= ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('17',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ~ ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
        | ~ ( v3_pre_topc @ X16 @ X15 )
        | ( ( k1_tops_1 @ X15 @ X16 )
          = X16 ) )
    | ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X15 )
      | ( ( k1_tops_1 @ X15 @ X16 )
        = X16 ) ) ),
    inference('sat_resolution*',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X15 )
      | ( ( k1_tops_1 @ X15 @ X16 )
        = X16 ) ) ),
    inference(simpl_trail,[status(thm)],['14','22'])).

thf('24',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_hidden @ X19 @ ( k1_tops_1 @ X20 @ X21 ) )
      | ( m1_connsp_2 @ X21 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ sk_C_1 @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X23 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X23 @ sk_B ) )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X23 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X23 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X23 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X23 @ sk_A @ sk_C_1 )
          | ~ ( r1_tarski @ X23 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','4','46'])).

thf('48',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k1_tops_1 @ X18 @ X17 )
       != X17 )
      | ( v3_pre_topc @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('51',plain,
    ( ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 )
        | ( ( k1_tops_1 @ X18 @ X17 )
         != X17 )
        | ( v3_pre_topc @ X17 @ X18 ) )
   <= ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 )
        | ( ( k1_tops_1 @ X18 @ X17 )
         != X17 )
        | ( v3_pre_topc @ X17 @ X18 ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
   <= ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(split,[status(esa)],['50'])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ~ ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 )
        | ( ( k1_tops_1 @ X18 @ X17 )
         != X17 )
        | ( v3_pre_topc @ X17 @ X18 ) )
    | ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(split,[status(esa)],['50'])).

thf('58',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( ( k1_tops_1 @ X18 @ X17 )
       != X17 )
      | ( v3_pre_topc @ X17 @ X18 ) ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( ( k1_tops_1 @ X18 @ X17 )
       != X17 )
      | ( v3_pre_topc @ X17 @ X18 ) ) ),
    inference(simpl_trail,[status(thm)],['51','58'])).

thf('60',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['49','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X11 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('71',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('75',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X22 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D @ X22 ) @ sk_A @ X22 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X22 ) @ sk_A @ X22 ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X22 ) @ sk_A @ X22 ) ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,
    ( ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X22 ) @ sk_A @ X22 ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['75'])).

thf('78',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X22 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D @ X22 ) @ sk_A @ X22 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','46','77'])).

thf('79',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X22 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D @ X22 ) @ sk_A @ X22 ) ) ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('81',plain,(
    ! [X22: $i] :
      ( ( m1_connsp_2 @ ( sk_D @ X22 ) @ sk_A @ X22 )
      | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ ( sk_C @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('84',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X22 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('87',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_connsp_2 @ X21 @ X20 @ X19 )
      | ( r2_hidden @ X19 @ ( k1_tops_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('90',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ X1 )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ X1 )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['84'])).

thf('95',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X22 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','46','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['93','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('105',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ( r1_tarski @ ( k1_tops_1 @ X13 @ X12 ) @ ( k1_tops_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('106',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X22 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','46','94'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) ) ),
    inference(simpl_trail,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('113',plain,
    ( ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X22 ) @ sk_B ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X22 ) @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X22 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X22 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,
    ( ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X22 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X22 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('118',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X22 @ sk_B )
      | ( r1_tarski @ ( sk_D @ X22 ) @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','46','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['116','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['111','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('126',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['70','127'])).

thf('129',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['63','128'])).

thf('130',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['48','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oJzAtsSUsT
% 0.15/0.36  % Computer   : n001.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 21:25:01 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 336 iterations in 0.171s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.61  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.38/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.61  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.38/0.61  thf(sk_D_type, type, sk_D: $i > $i).
% 0.38/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.38/0.61  thf(t9_connsp_2, conjecture,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61           ( ( v3_pre_topc @ B @ A ) <=>
% 0.38/0.61             ( ![C:$i]:
% 0.38/0.61               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.61                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.38/0.61                      ( ![D:$i]:
% 0.38/0.61                        ( ( m1_subset_1 @
% 0.38/0.61                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.38/0.61                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i]:
% 0.38/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.61            ( l1_pre_topc @ A ) ) =>
% 0.38/0.61          ( ![B:$i]:
% 0.38/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61              ( ( v3_pre_topc @ B @ A ) <=>
% 0.38/0.61                ( ![C:$i]:
% 0.38/0.61                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.61                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.38/0.61                         ( ![D:$i]:
% 0.38/0.61                           ( ( m1_subset_1 @
% 0.38/0.61                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61                             ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.38/0.61                                  ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t9_connsp_2])).
% 0.38/0.61  thf('0', plain,
% 0.38/0.61      (![X23 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61          | ~ (m1_connsp_2 @ X23 @ sk_A @ sk_C_1)
% 0.38/0.61          | ~ (r1_tarski @ X23 @ sk_B)
% 0.38/0.61          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('1', plain,
% 0.38/0.61      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.61      inference('split', [status(esa)], ['0'])).
% 0.38/0.61  thf('2', plain,
% 0.38/0.61      ((![X23 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61           | ~ (m1_connsp_2 @ X23 @ sk_A @ sk_C_1)
% 0.38/0.61           | ~ (r1_tarski @ X23 @ sk_B))) | 
% 0.38/0.61       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.61      inference('split', [status(esa)], ['0'])).
% 0.38/0.61  thf('3', plain,
% 0.38/0.61      (((r2_hidden @ sk_C_1 @ sk_B) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('4', plain,
% 0.38/0.61      (~ ((v3_pre_topc @ sk_B @ sk_A)) | ((r2_hidden @ sk_C_1 @ sk_B))),
% 0.38/0.61      inference('split', [status(esa)], ['3'])).
% 0.38/0.61  thf('5', plain,
% 0.38/0.61      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 0.38/0.61      inference('split', [status(esa)], ['3'])).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t4_subset, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.38/0.61       ( m1_subset_1 @ A @ C ) ))).
% 0.38/0.61  thf('7', plain,
% 0.38/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X7 @ X8)
% 0.38/0.61          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.38/0.61          | (m1_subset_1 @ X7 @ X9))),
% 0.38/0.61      inference('cnf', [status(esa)], [t4_subset])).
% 0.38/0.61  thf('8', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.61  thf('9', plain,
% 0.38/0.61      (((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61         <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['5', '8'])).
% 0.38/0.61  thf('10', plain,
% 0.38/0.61      (![X22 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61          | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61          | (r1_tarski @ (sk_D @ X22) @ sk_B)
% 0.38/0.61          | (v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.61      inference('split', [status(esa)], ['10'])).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t55_tops_1, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( l1_pre_topc @ B ) =>
% 0.38/0.61           ( ![C:$i]:
% 0.38/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61               ( ![D:$i]:
% 0.38/0.61                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.38/0.61                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.38/0.61                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.38/0.61                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.38/0.61                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ X15)
% 0.38/0.61          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.61          | ~ (v3_pre_topc @ X16 @ X15)
% 0.38/0.61          | ((k1_tops_1 @ X15 @ X16) = (X16))
% 0.38/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.61          | ~ (l1_pre_topc @ X18)
% 0.38/0.61          | ~ (v2_pre_topc @ X18))),
% 0.38/0.61      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      ((![X15 : $i, X16 : $i]:
% 0.38/0.61          (~ (l1_pre_topc @ X15)
% 0.38/0.61           | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.61           | ~ (v3_pre_topc @ X16 @ X15)
% 0.38/0.61           | ((k1_tops_1 @ X15 @ X16) = (X16))))
% 0.38/0.61         <= ((![X15 : $i, X16 : $i]:
% 0.38/0.61                (~ (l1_pre_topc @ X15)
% 0.38/0.61                 | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.61                 | ~ (v3_pre_topc @ X16 @ X15)
% 0.38/0.61                 | ((k1_tops_1 @ X15 @ X16) = (X16)))))),
% 0.38/0.61      inference('split', [status(esa)], ['13'])).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      ((![X17 : $i, X18 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.61           | ~ (l1_pre_topc @ X18)
% 0.38/0.61           | ~ (v2_pre_topc @ X18)))
% 0.38/0.61         <= ((![X17 : $i, X18 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.61                 | ~ (l1_pre_topc @ X18)
% 0.38/0.61                 | ~ (v2_pre_topc @ X18))))),
% 0.38/0.61      inference('split', [status(esa)], ['13'])).
% 0.38/0.61  thf('17', plain,
% 0.38/0.61      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.38/0.61         <= ((![X17 : $i, X18 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.61                 | ~ (l1_pre_topc @ X18)
% 0.38/0.61                 | ~ (v2_pre_topc @ X18))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.61  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('20', plain,
% 0.38/0.61      (~
% 0.38/0.61       (![X17 : $i, X18 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.61           | ~ (l1_pre_topc @ X18)
% 0.38/0.61           | ~ (v2_pre_topc @ X18)))),
% 0.38/0.61      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.38/0.61  thf('21', plain,
% 0.38/0.61      ((![X15 : $i, X16 : $i]:
% 0.38/0.61          (~ (l1_pre_topc @ X15)
% 0.38/0.61           | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.61           | ~ (v3_pre_topc @ X16 @ X15)
% 0.38/0.61           | ((k1_tops_1 @ X15 @ X16) = (X16)))) | 
% 0.38/0.61       (![X17 : $i, X18 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.61           | ~ (l1_pre_topc @ X18)
% 0.38/0.61           | ~ (v2_pre_topc @ X18)))),
% 0.38/0.61      inference('split', [status(esa)], ['13'])).
% 0.38/0.61  thf('22', plain,
% 0.38/0.61      ((![X15 : $i, X16 : $i]:
% 0.38/0.61          (~ (l1_pre_topc @ X15)
% 0.38/0.61           | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.61           | ~ (v3_pre_topc @ X16 @ X15)
% 0.38/0.61           | ((k1_tops_1 @ X15 @ X16) = (X16))))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)], ['20', '21'])).
% 0.38/0.61  thf('23', plain,
% 0.38/0.61      (![X15 : $i, X16 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ X15)
% 0.38/0.61          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.61          | ~ (v3_pre_topc @ X16 @ X15)
% 0.38/0.61          | ((k1_tops_1 @ X15 @ X16) = (X16)))),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['14', '22'])).
% 0.38/0.61  thf('24', plain,
% 0.38/0.61      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.38/0.61        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.38/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['12', '23'])).
% 0.38/0.61  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('26', plain,
% 0.38/0.61      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.61  thf('27', plain,
% 0.38/0.61      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.38/0.61         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['11', '26'])).
% 0.38/0.61  thf('28', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(d1_connsp_2, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.61           ( ![C:$i]:
% 0.38/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.38/0.61                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.38/0.61  thf('29', plain,
% 0.38/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.38/0.61          | ~ (r2_hidden @ X19 @ (k1_tops_1 @ X20 @ X21))
% 0.38/0.61          | (m1_connsp_2 @ X21 @ X20 @ X19)
% 0.38/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.61          | ~ (l1_pre_topc @ X20)
% 0.38/0.61          | ~ (v2_pre_topc @ X20)
% 0.38/0.61          | (v2_struct_0 @ X20))),
% 0.38/0.61      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.38/0.61  thf('30', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v2_struct_0 @ sk_A)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 0.38/0.61          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.38/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.61  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('33', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v2_struct_0 @ sk_A)
% 0.38/0.61          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 0.38/0.61          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.38/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.38/0.61  thf('34', plain,
% 0.38/0.61      ((![X0 : $i]:
% 0.38/0.61          (~ (r2_hidden @ X0 @ sk_B)
% 0.38/0.61           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.61           | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 0.38/0.61           | (v2_struct_0 @ sk_A)))
% 0.38/0.61         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['27', '33'])).
% 0.38/0.61  thf('35', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A)
% 0.38/0.61         | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)
% 0.38/0.61         | ~ (r2_hidden @ sk_C_1 @ sk_B)))
% 0.38/0.61         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['9', '34'])).
% 0.38/0.61  thf('36', plain,
% 0.38/0.61      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 0.38/0.61      inference('split', [status(esa)], ['3'])).
% 0.38/0.61  thf('37', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)))
% 0.38/0.61         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 0.38/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.38/0.61  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('39', plain,
% 0.38/0.61      (((m1_connsp_2 @ sk_B @ sk_A @ sk_C_1))
% 0.38/0.61         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['37', '38'])).
% 0.38/0.61  thf('40', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('41', plain,
% 0.38/0.61      ((![X23 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61           | ~ (m1_connsp_2 @ X23 @ sk_A @ sk_C_1)
% 0.38/0.61           | ~ (r1_tarski @ X23 @ sk_B)))
% 0.38/0.61         <= ((![X23 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61                 | ~ (m1_connsp_2 @ X23 @ sk_A @ sk_C_1)
% 0.38/0.61                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.38/0.61      inference('split', [status(esa)], ['0'])).
% 0.38/0.61  thf('42', plain,
% 0.38/0.61      (((~ (r1_tarski @ sk_B @ sk_B) | ~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)))
% 0.38/0.61         <= ((![X23 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61                 | ~ (m1_connsp_2 @ X23 @ sk_A @ sk_C_1)
% 0.38/0.61                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.61  thf(d10_xboole_0, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.61  thf('43', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.61  thf('44', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.38/0.61      inference('simplify', [status(thm)], ['43'])).
% 0.38/0.61  thf('45', plain,
% 0.38/0.61      ((~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1))
% 0.38/0.61         <= ((![X23 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61                 | ~ (m1_connsp_2 @ X23 @ sk_A @ sk_C_1)
% 0.38/0.61                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.38/0.61      inference('demod', [status(thm)], ['42', '44'])).
% 0.38/0.61  thf('46', plain,
% 0.38/0.61      (~ ((r2_hidden @ sk_C_1 @ sk_B)) | 
% 0.38/0.61       ~
% 0.38/0.61       (![X23 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61           | ~ (m1_connsp_2 @ X23 @ sk_A @ sk_C_1)
% 0.38/0.61           | ~ (r1_tarski @ X23 @ sk_B))) | 
% 0.38/0.61       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['39', '45'])).
% 0.38/0.61  thf('47', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)], ['2', '4', '46'])).
% 0.38/0.61  thf('48', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['1', '47'])).
% 0.38/0.61  thf('49', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('50', plain,
% 0.38/0.61      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ X15)
% 0.38/0.61          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.61          | ((k1_tops_1 @ X18 @ X17) != (X17))
% 0.38/0.61          | (v3_pre_topc @ X17 @ X18)
% 0.38/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.61          | ~ (l1_pre_topc @ X18)
% 0.38/0.61          | ~ (v2_pre_topc @ X18))),
% 0.38/0.61      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.38/0.61  thf('51', plain,
% 0.38/0.61      ((![X17 : $i, X18 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.61           | ~ (l1_pre_topc @ X18)
% 0.38/0.61           | ~ (v2_pre_topc @ X18)
% 0.38/0.61           | ((k1_tops_1 @ X18 @ X17) != (X17))
% 0.38/0.61           | (v3_pre_topc @ X17 @ X18)))
% 0.38/0.61         <= ((![X17 : $i, X18 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.61                 | ~ (l1_pre_topc @ X18)
% 0.38/0.61                 | ~ (v2_pre_topc @ X18)
% 0.38/0.61                 | ((k1_tops_1 @ X18 @ X17) != (X17))
% 0.38/0.61                 | (v3_pre_topc @ X17 @ X18))))),
% 0.38/0.61      inference('split', [status(esa)], ['50'])).
% 0.38/0.61  thf('52', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('53', plain,
% 0.38/0.61      ((![X15 : $i, X16 : $i]:
% 0.38/0.61          (~ (l1_pre_topc @ X15)
% 0.38/0.61           | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))))
% 0.38/0.61         <= ((![X15 : $i, X16 : $i]:
% 0.38/0.61                (~ (l1_pre_topc @ X15)
% 0.38/0.61                 | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))))),
% 0.38/0.61      inference('split', [status(esa)], ['50'])).
% 0.38/0.61  thf('54', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A))
% 0.38/0.61         <= ((![X15 : $i, X16 : $i]:
% 0.38/0.61                (~ (l1_pre_topc @ X15)
% 0.38/0.61                 | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.61  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('56', plain,
% 0.38/0.61      (~
% 0.38/0.61       (![X15 : $i, X16 : $i]:
% 0.38/0.61          (~ (l1_pre_topc @ X15)
% 0.38/0.61           | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))))),
% 0.38/0.61      inference('demod', [status(thm)], ['54', '55'])).
% 0.38/0.61  thf('57', plain,
% 0.38/0.61      ((![X17 : $i, X18 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.61           | ~ (l1_pre_topc @ X18)
% 0.38/0.61           | ~ (v2_pre_topc @ X18)
% 0.38/0.61           | ((k1_tops_1 @ X18 @ X17) != (X17))
% 0.38/0.61           | (v3_pre_topc @ X17 @ X18))) | 
% 0.38/0.61       (![X15 : $i, X16 : $i]:
% 0.38/0.61          (~ (l1_pre_topc @ X15)
% 0.38/0.61           | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))))),
% 0.38/0.61      inference('split', [status(esa)], ['50'])).
% 0.38/0.61  thf('58', plain,
% 0.38/0.61      ((![X17 : $i, X18 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.61           | ~ (l1_pre_topc @ X18)
% 0.38/0.61           | ~ (v2_pre_topc @ X18)
% 0.38/0.61           | ((k1_tops_1 @ X18 @ X17) != (X17))
% 0.38/0.61           | (v3_pre_topc @ X17 @ X18)))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.38/0.61  thf('59', plain,
% 0.38/0.61      (![X17 : $i, X18 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.61          | ~ (l1_pre_topc @ X18)
% 0.38/0.61          | ~ (v2_pre_topc @ X18)
% 0.38/0.61          | ((k1_tops_1 @ X18 @ X17) != (X17))
% 0.38/0.61          | (v3_pre_topc @ X17 @ X18))),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['51', '58'])).
% 0.38/0.61  thf('60', plain,
% 0.38/0.61      (((v3_pre_topc @ sk_B @ sk_A)
% 0.38/0.61        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 0.38/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['49', '59'])).
% 0.38/0.61  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('63', plain,
% 0.38/0.61      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 0.38/0.61      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.38/0.61  thf('64', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t44_tops_1, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.38/0.61  thf('65', plain,
% 0.38/0.61      (![X10 : $i, X11 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.61          | (r1_tarski @ (k1_tops_1 @ X11 @ X10) @ X10)
% 0.38/0.61          | ~ (l1_pre_topc @ X11))),
% 0.38/0.61      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.38/0.61  thf('66', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.38/0.61  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('68', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.38/0.61      inference('demod', [status(thm)], ['66', '67'])).
% 0.38/0.61  thf('69', plain,
% 0.38/0.61      (![X4 : $i, X6 : $i]:
% 0.38/0.61         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.61  thf('70', plain,
% 0.38/0.61      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.38/0.61        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.61  thf(d3_tarski, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.61  thf('71', plain,
% 0.38/0.61      (![X1 : $i, X3 : $i]:
% 0.38/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.61  thf('72', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.61  thf('73', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((r1_tarski @ sk_B @ X0)
% 0.38/0.61          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.61  thf('74', plain,
% 0.38/0.61      (![X1 : $i, X3 : $i]:
% 0.38/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.61  thf('75', plain,
% 0.38/0.61      (![X22 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61          | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61          | (m1_connsp_2 @ (sk_D @ X22) @ sk_A @ X22)
% 0.38/0.61          | (v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('76', plain,
% 0.38/0.61      ((![X22 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61           | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61           | (m1_connsp_2 @ (sk_D @ X22) @ sk_A @ X22)))
% 0.38/0.61         <= ((![X22 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61                 | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61                 | (m1_connsp_2 @ (sk_D @ X22) @ sk_A @ X22))))),
% 0.38/0.61      inference('split', [status(esa)], ['75'])).
% 0.38/0.61  thf('77', plain,
% 0.38/0.61      ((![X22 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61           | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61           | (m1_connsp_2 @ (sk_D @ X22) @ sk_A @ X22))) | 
% 0.38/0.61       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.61      inference('split', [status(esa)], ['75'])).
% 0.38/0.61  thf('78', plain,
% 0.38/0.61      ((![X22 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61           | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61           | (m1_connsp_2 @ (sk_D @ X22) @ sk_A @ X22)))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)], ['2', '4', '46', '77'])).
% 0.38/0.61  thf('79', plain,
% 0.38/0.61      (![X22 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61          | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61          | (m1_connsp_2 @ (sk_D @ X22) @ sk_A @ X22))),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['76', '78'])).
% 0.38/0.61  thf('80', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.61  thf('81', plain,
% 0.38/0.61      (![X22 : $i]:
% 0.38/0.61         ((m1_connsp_2 @ (sk_D @ X22) @ sk_A @ X22)
% 0.38/0.61          | ~ (r2_hidden @ X22 @ sk_B))),
% 0.38/0.61      inference('clc', [status(thm)], ['79', '80'])).
% 0.38/0.61  thf('82', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((r1_tarski @ sk_B @ X0)
% 0.38/0.61          | (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ 
% 0.38/0.61             (sk_C @ X0 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['74', '81'])).
% 0.38/0.61  thf('83', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((r1_tarski @ sk_B @ X0)
% 0.38/0.61          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.61  thf('84', plain,
% 0.38/0.61      (![X22 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61          | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61          | (m1_subset_1 @ (sk_D @ X22) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61          | (v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('85', plain,
% 0.38/0.61      ((![X22 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61           | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61           | (m1_subset_1 @ (sk_D @ X22) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.38/0.61         <= ((![X22 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61                 | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61                 | (m1_subset_1 @ (sk_D @ X22) @ 
% 0.38/0.61                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.61      inference('split', [status(esa)], ['84'])).
% 0.38/0.61  thf('86', plain,
% 0.38/0.61      ((![X0 : $i]:
% 0.38/0.61          ((r1_tarski @ sk_B @ X0)
% 0.38/0.61           | (m1_subset_1 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 0.38/0.61              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61           | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B)))
% 0.38/0.61         <= ((![X22 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61                 | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61                 | (m1_subset_1 @ (sk_D @ X22) @ 
% 0.38/0.61                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['83', '85'])).
% 0.38/0.61  thf('87', plain,
% 0.38/0.61      (![X1 : $i, X3 : $i]:
% 0.38/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.61  thf('88', plain,
% 0.38/0.61      ((![X0 : $i]:
% 0.38/0.61          ((m1_subset_1 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 0.38/0.61            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61           | (r1_tarski @ sk_B @ X0)))
% 0.38/0.61         <= ((![X22 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61                 | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61                 | (m1_subset_1 @ (sk_D @ X22) @ 
% 0.38/0.61                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.61      inference('clc', [status(thm)], ['86', '87'])).
% 0.38/0.61  thf('89', plain,
% 0.38/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.38/0.61          | ~ (m1_connsp_2 @ X21 @ X20 @ X19)
% 0.38/0.61          | (r2_hidden @ X19 @ (k1_tops_1 @ X20 @ X21))
% 0.38/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.61          | ~ (l1_pre_topc @ X20)
% 0.38/0.61          | ~ (v2_pre_topc @ X20)
% 0.38/0.61          | (v2_struct_0 @ X20))),
% 0.38/0.61      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.38/0.61  thf('90', plain,
% 0.38/0.61      ((![X0 : $i, X1 : $i]:
% 0.38/0.61          ((r1_tarski @ sk_B @ X0)
% 0.38/0.61           | (v2_struct_0 @ sk_A)
% 0.38/0.61           | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61           | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61           | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 0.38/0.61           | ~ (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ X1)
% 0.38/0.61           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.61         <= ((![X22 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61                 | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61                 | (m1_subset_1 @ (sk_D @ X22) @ 
% 0.38/0.61                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['88', '89'])).
% 0.38/0.61  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('93', plain,
% 0.38/0.61      ((![X0 : $i, X1 : $i]:
% 0.38/0.61          ((r1_tarski @ sk_B @ X0)
% 0.38/0.61           | (v2_struct_0 @ sk_A)
% 0.38/0.61           | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 0.38/0.61           | ~ (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ X1)
% 0.38/0.61           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.61         <= ((![X22 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61                 | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61                 | (m1_subset_1 @ (sk_D @ X22) @ 
% 0.38/0.61                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.61      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.38/0.61  thf('94', plain,
% 0.38/0.61      ((![X22 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61           | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61           | (m1_subset_1 @ (sk_D @ X22) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 0.38/0.61       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.61      inference('split', [status(esa)], ['84'])).
% 0.38/0.61  thf('95', plain,
% 0.38/0.61      ((![X22 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61           | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61           | (m1_subset_1 @ (sk_D @ X22) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)], ['2', '4', '46', '94'])).
% 0.38/0.61  thf('96', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((r1_tarski @ sk_B @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 0.38/0.61          | ~ (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ X1)
% 0.38/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['93', '95'])).
% 0.38/0.61  thf('97', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((r1_tarski @ sk_B @ X0)
% 0.38/0.61          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.38/0.61          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 0.38/0.61             (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | (r1_tarski @ sk_B @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['82', '96'])).
% 0.38/0.61  thf('98', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v2_struct_0 @ sk_A)
% 0.38/0.61          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 0.38/0.61             (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 0.38/0.61          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.38/0.61          | (r1_tarski @ sk_B @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['97'])).
% 0.38/0.61  thf('99', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((r1_tarski @ sk_B @ X0)
% 0.38/0.61          | (r1_tarski @ sk_B @ X0)
% 0.38/0.61          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 0.38/0.61             (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['73', '98'])).
% 0.38/0.61  thf('100', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v2_struct_0 @ sk_A)
% 0.38/0.61          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 0.38/0.61             (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 0.38/0.61          | (r1_tarski @ sk_B @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['99'])).
% 0.38/0.61  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('102', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((r1_tarski @ sk_B @ X0)
% 0.38/0.61          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 0.38/0.61             (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B)))))),
% 0.38/0.61      inference('clc', [status(thm)], ['100', '101'])).
% 0.38/0.61  thf('103', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('104', plain,
% 0.38/0.61      ((![X0 : $i]:
% 0.38/0.61          ((m1_subset_1 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 0.38/0.61            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61           | (r1_tarski @ sk_B @ X0)))
% 0.38/0.61         <= ((![X22 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61                 | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61                 | (m1_subset_1 @ (sk_D @ X22) @ 
% 0.38/0.61                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.61      inference('clc', [status(thm)], ['86', '87'])).
% 0.38/0.61  thf(t48_tops_1, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61           ( ![C:$i]:
% 0.38/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61               ( ( r1_tarski @ B @ C ) =>
% 0.38/0.61                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.38/0.61  thf('105', plain,
% 0.38/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.38/0.61          | ~ (r1_tarski @ X12 @ X14)
% 0.38/0.61          | (r1_tarski @ (k1_tops_1 @ X13 @ X12) @ (k1_tops_1 @ X13 @ X14))
% 0.38/0.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.38/0.61          | ~ (l1_pre_topc @ X13))),
% 0.38/0.61      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.38/0.61  thf('106', plain,
% 0.38/0.61      ((![X0 : $i, X1 : $i]:
% 0.38/0.61          ((r1_tarski @ sk_B @ X0)
% 0.38/0.61           | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61           | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 0.38/0.61              (k1_tops_1 @ sk_A @ X1))
% 0.38/0.61           | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)))
% 0.38/0.61         <= ((![X22 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61                 | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61                 | (m1_subset_1 @ (sk_D @ X22) @ 
% 0.38/0.61                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['104', '105'])).
% 0.38/0.61  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('108', plain,
% 0.38/0.61      ((![X0 : $i, X1 : $i]:
% 0.38/0.61          ((r1_tarski @ sk_B @ X0)
% 0.38/0.61           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61           | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 0.38/0.61              (k1_tops_1 @ sk_A @ X1))
% 0.38/0.61           | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)))
% 0.38/0.61         <= ((![X22 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61                 | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61                 | (m1_subset_1 @ (sk_D @ X22) @ 
% 0.38/0.61                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.61      inference('demod', [status(thm)], ['106', '107'])).
% 0.38/0.61  thf('109', plain,
% 0.38/0.61      ((![X22 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61           | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61           | (m1_subset_1 @ (sk_D @ X22) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)], ['2', '4', '46', '94'])).
% 0.38/0.61  thf('110', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((r1_tarski @ sk_B @ X0)
% 0.38/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 0.38/0.61             (k1_tops_1 @ sk_A @ X1))
% 0.38/0.61          | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1))),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['108', '109'])).
% 0.38/0.61  thf('111', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 0.38/0.61          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 0.38/0.61             (k1_tops_1 @ sk_A @ sk_B))
% 0.38/0.61          | (r1_tarski @ sk_B @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['103', '110'])).
% 0.38/0.61  thf('112', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((r1_tarski @ sk_B @ X0)
% 0.38/0.61          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.61  thf('113', plain,
% 0.38/0.61      ((![X22 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61           | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61           | (r1_tarski @ (sk_D @ X22) @ sk_B)))
% 0.38/0.61         <= ((![X22 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61                 | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61                 | (r1_tarski @ (sk_D @ X22) @ sk_B))))),
% 0.38/0.61      inference('split', [status(esa)], ['10'])).
% 0.38/0.61  thf('114', plain,
% 0.38/0.61      ((![X0 : $i]:
% 0.38/0.61          ((r1_tarski @ sk_B @ X0)
% 0.38/0.61           | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 0.38/0.61           | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B)))
% 0.38/0.61         <= ((![X22 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61                 | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61                 | (r1_tarski @ (sk_D @ X22) @ sk_B))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['112', '113'])).
% 0.38/0.61  thf('115', plain,
% 0.38/0.61      (![X1 : $i, X3 : $i]:
% 0.38/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.61  thf('116', plain,
% 0.38/0.61      ((![X0 : $i]:
% 0.38/0.61          ((r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 0.38/0.61           | (r1_tarski @ sk_B @ X0)))
% 0.38/0.61         <= ((![X22 : $i]:
% 0.38/0.61                (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61                 | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61                 | (r1_tarski @ (sk_D @ X22) @ sk_B))))),
% 0.38/0.61      inference('clc', [status(thm)], ['114', '115'])).
% 0.38/0.61  thf('117', plain,
% 0.38/0.61      ((![X22 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61           | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.61           | (r1_tarski @ (sk_D @ X22) @ sk_B))) | 
% 0.38/0.61       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.61      inference('split', [status(esa)], ['10'])).
% 0.38/0.61  thf('118', plain,
% 0.38/0.61      ((![X22 : $i]:
% 0.38/0.61          (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A))
% 0.38/0.61           | ~ (r2_hidden @ X22 @ sk_B)
% 0.38/0.62           | (r1_tarski @ (sk_D @ X22) @ sk_B)))),
% 0.38/0.62      inference('sat_resolution*', [status(thm)], ['2', '4', '46', '117'])).
% 0.38/0.62  thf('119', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 0.38/0.62          | (r1_tarski @ sk_B @ X0))),
% 0.38/0.62      inference('simpl_trail', [status(thm)], ['116', '118'])).
% 0.38/0.62  thf('120', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ sk_B @ X0)
% 0.38/0.62          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 0.38/0.62             (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['111', '119'])).
% 0.38/0.62  thf('121', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.62          | (r2_hidden @ X0 @ X2)
% 0.38/0.62          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.62  thf('122', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((r1_tarski @ sk_B @ X0)
% 0.38/0.62          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.38/0.62          | ~ (r2_hidden @ X1 @ 
% 0.38/0.62               (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B)))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['120', '121'])).
% 0.38/0.62  thf('123', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ sk_B @ X0)
% 0.38/0.62          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.38/0.62          | (r1_tarski @ sk_B @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['102', '122'])).
% 0.38/0.62  thf('124', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.38/0.62          | (r1_tarski @ sk_B @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['123'])).
% 0.38/0.62  thf('125', plain,
% 0.38/0.62      (![X1 : $i, X3 : $i]:
% 0.38/0.62         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.62  thf('126', plain,
% 0.38/0.62      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.38/0.62        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['124', '125'])).
% 0.38/0.62  thf('127', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 0.38/0.62      inference('simplify', [status(thm)], ['126'])).
% 0.38/0.62  thf('128', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['70', '127'])).
% 0.38/0.62  thf('129', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.38/0.62      inference('demod', [status(thm)], ['63', '128'])).
% 0.38/0.62  thf('130', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('simplify', [status(thm)], ['129'])).
% 0.38/0.62  thf('131', plain, ($false), inference('demod', [status(thm)], ['48', '130'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
