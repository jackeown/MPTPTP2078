%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yAdn87TtEx

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:07 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 627 expanded)
%              Number of leaves         :   32 ( 178 expanded)
%              Depth                    :   21
%              Number of atoms          : 1243 (10431 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t54_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
          <=> ? [D: $i] :
                ( ( r2_hidden @ B @ D )
                & ( r1_tarski @ D @ C )
                & ( v3_pre_topc @ D @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i,C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
            <=> ? [D: $i] :
                  ( ( r2_hidden @ B @ D )
                  & ( r1_tarski @ D @ C )
                  & ( v3_pre_topc @ D @ A )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_tops_1])).

thf('0',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X30 @ sk_A )
      | ~ ( r1_tarski @ X30 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X30 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X30 ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X30 @ sk_A )
      | ~ ( r1_tarski @ X30 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X30 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X30 ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X30 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X30 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X26 @ X25 ) @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X21 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('20',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
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
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X30 ) ) ),
    inference(demod,[status(thm)],['12','17','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X30 @ sk_A )
          | ~ ( r1_tarski @ X30 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X30 ) ) ),
    inference('sup-',[status(thm)],['4','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r1_tarski @ X27 @ X29 )
      | ( r1_tarski @ ( k1_tops_1 @ X28 @ X27 ) @ ( k1_tops_1 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X30 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['29'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['35','25','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['34','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['40'])).

thf('43',plain,(
    r1_tarski @ sk_D @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','25','42'])).

thf('44',plain,(
    r1_tarski @ sk_D @ sk_C ),
    inference(simpl_trail,[status(thm)],['41','43'])).

thf('45',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k1_tops_1 @ X18 @ X17 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_pre_topc @ X18 @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('48',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_D )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('52',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','36'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['54','55'])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('57',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X24 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['60'])).

thf('63',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','25','62'])).

thf('64',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['61','63'])).

thf('65',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['58','59','64'])).

thf('66',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','36'])).

thf('68',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['66','67'])).

thf('69',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['65','68'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('71',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('73',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_pre_topc @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('79',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','77','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['35','25','36'])).

thf('83',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('85',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('86',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('89',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['35','25','36'])).

thf('91',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = sk_D ),
    inference(simpl_trail,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = sk_D ),
    inference('sup+',[status(thm)],['83','91'])).

thf('93',plain,(
    r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['45','92'])).

thf('94',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['3'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('95',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X5 ) @ X7 )
      | ~ ( r2_hidden @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('96',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('100',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['2','25','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['98','100'])).

thf('102',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['93','101'])).

thf('103',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k1_tarski @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('104',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['27','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yAdn87TtEx
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 1.01/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.01/1.20  % Solved by: fo/fo7.sh
% 1.01/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.20  % done 1279 iterations in 0.751s
% 1.01/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.01/1.20  % SZS output start Refutation
% 1.01/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.20  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.01/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.20  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.01/1.20  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.01/1.20  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.01/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.01/1.20  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.01/1.20  thf(sk_D_type, type, sk_D: $i).
% 1.01/1.20  thf(sk_C_type, type, sk_C: $i).
% 1.01/1.20  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.01/1.20  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.01/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.01/1.20  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.01/1.20  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.01/1.20  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.01/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.01/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.01/1.20  thf(t54_tops_1, conjecture,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.20       ( ![B:$i,C:$i]:
% 1.01/1.20         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 1.01/1.20             ( ?[D:$i]:
% 1.01/1.20               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 1.01/1.20                 ( v3_pre_topc @ D @ A ) & 
% 1.01/1.20                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.01/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.20    (~( ![A:$i]:
% 1.01/1.20        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.20          ( ![B:$i,C:$i]:
% 1.01/1.20            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 1.01/1.20                ( ?[D:$i]:
% 1.01/1.20                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 1.01/1.20                    ( v3_pre_topc @ D @ A ) & 
% 1.01/1.20                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.01/1.20    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 1.01/1.20  thf('0', plain,
% 1.01/1.20      (![X30 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20          | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.01/1.20          | ~ (r1_tarski @ X30 @ sk_C)
% 1.01/1.20          | ~ (r2_hidden @ sk_B @ X30)
% 1.01/1.20          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('1', plain,
% 1.01/1.20      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 1.01/1.20         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 1.01/1.20      inference('split', [status(esa)], ['0'])).
% 1.01/1.20  thf('2', plain,
% 1.01/1.20      ((![X30 : $i]:
% 1.01/1.20          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20           | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.01/1.20           | ~ (r1_tarski @ X30 @ sk_C)
% 1.01/1.20           | ~ (r2_hidden @ sk_B @ X30))) | 
% 1.01/1.20       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.01/1.20      inference('split', [status(esa)], ['0'])).
% 1.01/1.20  thf('3', plain,
% 1.01/1.20      (((r2_hidden @ sk_B @ sk_D)
% 1.01/1.20        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('4', plain,
% 1.01/1.20      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 1.01/1.20         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 1.01/1.20      inference('split', [status(esa)], ['3'])).
% 1.01/1.20  thf('5', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(dt_k1_tops_1, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( ( l1_pre_topc @ A ) & 
% 1.01/1.20         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.01/1.20       ( m1_subset_1 @
% 1.01/1.20         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.01/1.20  thf('6', plain,
% 1.01/1.20      (![X19 : $i, X20 : $i]:
% 1.01/1.20         (~ (l1_pre_topc @ X19)
% 1.01/1.20          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.01/1.20          | (m1_subset_1 @ (k1_tops_1 @ X19 @ X20) @ 
% 1.01/1.20             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 1.01/1.20      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.01/1.20  thf('7', plain,
% 1.01/1.20      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 1.01/1.20         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20        | ~ (l1_pre_topc @ sk_A))),
% 1.01/1.20      inference('sup-', [status(thm)], ['5', '6'])).
% 1.01/1.20  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('9', plain,
% 1.01/1.20      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 1.01/1.20        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.20      inference('demod', [status(thm)], ['7', '8'])).
% 1.01/1.20  thf('10', plain,
% 1.01/1.20      (![X30 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20          | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.01/1.20          | ~ (r1_tarski @ X30 @ sk_C)
% 1.01/1.20          | ~ (r2_hidden @ sk_B @ X30)
% 1.01/1.20          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('11', plain,
% 1.01/1.20      ((![X30 : $i]:
% 1.01/1.20          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20           | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.01/1.20           | ~ (r1_tarski @ X30 @ sk_C)
% 1.01/1.20           | ~ (r2_hidden @ sk_B @ X30)))
% 1.01/1.20         <= ((![X30 : $i]:
% 1.01/1.20                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.01/1.20                 | ~ (r1_tarski @ X30 @ sk_C)
% 1.01/1.20                 | ~ (r2_hidden @ sk_B @ X30))))),
% 1.01/1.20      inference('split', [status(esa)], ['10'])).
% 1.01/1.20  thf('12', plain,
% 1.01/1.20      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 1.01/1.20         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 1.01/1.20         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 1.01/1.20         <= ((![X30 : $i]:
% 1.01/1.20                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.01/1.20                 | ~ (r1_tarski @ X30 @ sk_C)
% 1.01/1.20                 | ~ (r2_hidden @ sk_B @ X30))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['9', '11'])).
% 1.01/1.20  thf('13', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(t44_tops_1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( l1_pre_topc @ A ) =>
% 1.01/1.20       ( ![B:$i]:
% 1.01/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.01/1.20  thf('14', plain,
% 1.01/1.20      (![X25 : $i, X26 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.01/1.20          | (r1_tarski @ (k1_tops_1 @ X26 @ X25) @ X25)
% 1.01/1.20          | ~ (l1_pre_topc @ X26))),
% 1.01/1.20      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.01/1.20  thf('15', plain,
% 1.01/1.20      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 1.01/1.20      inference('sup-', [status(thm)], ['13', '14'])).
% 1.01/1.20  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('17', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 1.01/1.20      inference('demod', [status(thm)], ['15', '16'])).
% 1.01/1.20  thf('18', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(fc9_tops_1, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.01/1.20         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.01/1.20       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.01/1.20  thf('19', plain,
% 1.01/1.20      (![X21 : $i, X22 : $i]:
% 1.01/1.20         (~ (l1_pre_topc @ X21)
% 1.01/1.20          | ~ (v2_pre_topc @ X21)
% 1.01/1.20          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.01/1.20          | (v3_pre_topc @ (k1_tops_1 @ X21 @ X22) @ X21))),
% 1.01/1.20      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.01/1.20  thf('20', plain,
% 1.01/1.20      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 1.01/1.20        | ~ (v2_pre_topc @ sk_A)
% 1.01/1.20        | ~ (l1_pre_topc @ sk_A))),
% 1.01/1.20      inference('sup-', [status(thm)], ['18', '19'])).
% 1.01/1.20  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('23', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 1.01/1.20      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.01/1.20  thf('24', plain,
% 1.01/1.20      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 1.01/1.20         <= ((![X30 : $i]:
% 1.01/1.20                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.01/1.20                 | ~ (r1_tarski @ X30 @ sk_C)
% 1.01/1.20                 | ~ (r2_hidden @ sk_B @ X30))))),
% 1.01/1.20      inference('demod', [status(thm)], ['12', '17', '23'])).
% 1.01/1.20  thf('25', plain,
% 1.01/1.20      (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) | 
% 1.01/1.20       ~
% 1.01/1.20       (![X30 : $i]:
% 1.01/1.20          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20           | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.01/1.20           | ~ (r1_tarski @ X30 @ sk_C)
% 1.01/1.20           | ~ (r2_hidden @ sk_B @ X30)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['4', '24'])).
% 1.01/1.20  thf('26', plain, (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)], ['2', '25'])).
% 1.01/1.20  thf('27', plain, (~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 1.01/1.20  thf('28', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('29', plain,
% 1.01/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('30', plain,
% 1.01/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('split', [status(esa)], ['29'])).
% 1.01/1.20  thf(t48_tops_1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( l1_pre_topc @ A ) =>
% 1.01/1.20       ( ![B:$i]:
% 1.01/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20           ( ![C:$i]:
% 1.01/1.20             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20               ( ( r1_tarski @ B @ C ) =>
% 1.01/1.20                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.01/1.20  thf('31', plain,
% 1.01/1.20      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.01/1.20          | ~ (r1_tarski @ X27 @ X29)
% 1.01/1.20          | (r1_tarski @ (k1_tops_1 @ X28 @ X27) @ (k1_tops_1 @ X28 @ X29))
% 1.01/1.20          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.01/1.20          | ~ (l1_pre_topc @ X28))),
% 1.01/1.20      inference('cnf', [status(esa)], [t48_tops_1])).
% 1.01/1.20  thf('32', plain,
% 1.01/1.20      ((![X0 : $i]:
% 1.01/1.20          (~ (l1_pre_topc @ sk_A)
% 1.01/1.20           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 1.01/1.20           | ~ (r1_tarski @ sk_D @ X0)))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['30', '31'])).
% 1.01/1.20  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('34', plain,
% 1.01/1.20      ((![X0 : $i]:
% 1.01/1.20          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 1.01/1.20           | ~ (r1_tarski @ sk_D @ X0)))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('demod', [status(thm)], ['32', '33'])).
% 1.01/1.20  thf('35', plain,
% 1.01/1.20      (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) | 
% 1.01/1.20       (![X30 : $i]:
% 1.01/1.20          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20           | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.01/1.20           | ~ (r1_tarski @ X30 @ sk_C)
% 1.01/1.20           | ~ (r2_hidden @ sk_B @ X30)))),
% 1.01/1.20      inference('split', [status(esa)], ['0'])).
% 1.01/1.20  thf('36', plain,
% 1.01/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 1.01/1.20       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.01/1.20      inference('split', [status(esa)], ['29'])).
% 1.01/1.20  thf('37', plain,
% 1.01/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)], ['35', '25', '36'])).
% 1.01/1.20  thf('38', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 1.01/1.20          | ~ (r1_tarski @ sk_D @ X0))),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['34', '37'])).
% 1.01/1.20  thf('39', plain,
% 1.01/1.20      ((~ (r1_tarski @ sk_D @ sk_C)
% 1.01/1.20        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['28', '38'])).
% 1.01/1.20  thf('40', plain,
% 1.01/1.20      (((r1_tarski @ sk_D @ sk_C)
% 1.01/1.20        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('41', plain,
% 1.01/1.20      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 1.01/1.20      inference('split', [status(esa)], ['40'])).
% 1.01/1.20  thf('42', plain,
% 1.01/1.20      (((r1_tarski @ sk_D @ sk_C)) | 
% 1.01/1.20       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.01/1.20      inference('split', [status(esa)], ['40'])).
% 1.01/1.20  thf('43', plain, (((r1_tarski @ sk_D @ sk_C))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)], ['2', '25', '42'])).
% 1.01/1.20  thf('44', plain, ((r1_tarski @ sk_D @ sk_C)),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['41', '43'])).
% 1.01/1.20  thf('45', plain,
% 1.01/1.20      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C))),
% 1.01/1.20      inference('demod', [status(thm)], ['39', '44'])).
% 1.01/1.20  thf('46', plain,
% 1.01/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('split', [status(esa)], ['29'])).
% 1.01/1.20  thf(d1_tops_1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( l1_pre_topc @ A ) =>
% 1.01/1.20       ( ![B:$i]:
% 1.01/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20           ( ( k1_tops_1 @ A @ B ) =
% 1.01/1.20             ( k3_subset_1 @
% 1.01/1.20               ( u1_struct_0 @ A ) @ 
% 1.01/1.20               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.01/1.20  thf('47', plain,
% 1.01/1.20      (![X17 : $i, X18 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.01/1.20          | ((k1_tops_1 @ X18 @ X17)
% 1.01/1.20              = (k3_subset_1 @ (u1_struct_0 @ X18) @ 
% 1.01/1.20                 (k2_pre_topc @ X18 @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X17))))
% 1.01/1.20          | ~ (l1_pre_topc @ X18))),
% 1.01/1.20      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.01/1.20  thf('48', plain,
% 1.01/1.20      (((~ (l1_pre_topc @ sk_A)
% 1.01/1.20         | ((k1_tops_1 @ sk_A @ sk_D)
% 1.01/1.20             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.01/1.20                (k2_pre_topc @ sk_A @ 
% 1.01/1.20                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['46', '47'])).
% 1.01/1.20  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('50', plain,
% 1.01/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('split', [status(esa)], ['29'])).
% 1.01/1.20  thf(d5_subset_1, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.01/1.20       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.01/1.20  thf('51', plain,
% 1.01/1.20      (![X8 : $i, X9 : $i]:
% 1.01/1.20         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 1.01/1.20          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 1.01/1.20      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.01/1.20  thf('52', plain,
% 1.01/1.20      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 1.01/1.20          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['50', '51'])).
% 1.01/1.20  thf('53', plain,
% 1.01/1.20      ((((k1_tops_1 @ sk_A @ sk_D)
% 1.01/1.20          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.01/1.20             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('demod', [status(thm)], ['48', '49', '52'])).
% 1.01/1.20  thf('54', plain,
% 1.01/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('split', [status(esa)], ['29'])).
% 1.01/1.20  thf('55', plain,
% 1.01/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)], ['2', '25', '36'])).
% 1.01/1.20  thf('56', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['54', '55'])).
% 1.01/1.20  thf(t30_tops_1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( l1_pre_topc @ A ) =>
% 1.01/1.20       ( ![B:$i]:
% 1.01/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20           ( ( v3_pre_topc @ B @ A ) <=>
% 1.01/1.20             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.01/1.20  thf('57', plain,
% 1.01/1.20      (![X23 : $i, X24 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.01/1.20          | ~ (v3_pre_topc @ X23 @ X24)
% 1.01/1.20          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 1.01/1.20          | ~ (l1_pre_topc @ X24))),
% 1.01/1.20      inference('cnf', [status(esa)], [t30_tops_1])).
% 1.01/1.20  thf('58', plain,
% 1.01/1.20      ((~ (l1_pre_topc @ sk_A)
% 1.01/1.20        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 1.01/1.20        | ~ (v3_pre_topc @ sk_D @ sk_A))),
% 1.01/1.20      inference('sup-', [status(thm)], ['56', '57'])).
% 1.01/1.20  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('60', plain,
% 1.01/1.20      (((v3_pre_topc @ sk_D @ sk_A)
% 1.01/1.20        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('61', plain,
% 1.01/1.20      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 1.01/1.20      inference('split', [status(esa)], ['60'])).
% 1.01/1.20  thf('62', plain,
% 1.01/1.20      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 1.01/1.20       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.01/1.20      inference('split', [status(esa)], ['60'])).
% 1.01/1.20  thf('63', plain, (((v3_pre_topc @ sk_D @ sk_A))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)], ['2', '25', '62'])).
% 1.01/1.20  thf('64', plain, ((v3_pre_topc @ sk_D @ sk_A)),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['61', '63'])).
% 1.01/1.20  thf('65', plain,
% 1.01/1.20      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)),
% 1.01/1.20      inference('demod', [status(thm)], ['58', '59', '64'])).
% 1.01/1.20  thf('66', plain,
% 1.01/1.20      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 1.01/1.20          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['50', '51'])).
% 1.01/1.20  thf('67', plain,
% 1.01/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)], ['2', '25', '36'])).
% 1.01/1.20  thf('68', plain,
% 1.01/1.20      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 1.01/1.20         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['66', '67'])).
% 1.01/1.20  thf('69', plain,
% 1.01/1.20      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)),
% 1.01/1.20      inference('demod', [status(thm)], ['65', '68'])).
% 1.01/1.20  thf(t36_xboole_1, axiom,
% 1.01/1.20    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.01/1.20  thf('70', plain,
% 1.01/1.20      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 1.01/1.20      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.01/1.20  thf(t3_subset, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.01/1.20  thf('71', plain,
% 1.01/1.20      (![X12 : $i, X14 : $i]:
% 1.01/1.20         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 1.01/1.20      inference('cnf', [status(esa)], [t3_subset])).
% 1.01/1.20  thf('72', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['70', '71'])).
% 1.01/1.20  thf(t52_pre_topc, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( l1_pre_topc @ A ) =>
% 1.01/1.20       ( ![B:$i]:
% 1.01/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.01/1.20             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.01/1.20               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.01/1.20  thf('73', plain,
% 1.01/1.20      (![X15 : $i, X16 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.01/1.20          | ~ (v4_pre_topc @ X15 @ X16)
% 1.01/1.20          | ((k2_pre_topc @ X16 @ X15) = (X15))
% 1.01/1.20          | ~ (l1_pre_topc @ X16))),
% 1.01/1.20      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.01/1.20  thf('74', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         (~ (l1_pre_topc @ X0)
% 1.01/1.20          | ((k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 1.01/1.20              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 1.01/1.20          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['72', '73'])).
% 1.01/1.20  thf('75', plain,
% 1.01/1.20      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))
% 1.01/1.20          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))
% 1.01/1.20        | ~ (l1_pre_topc @ sk_A))),
% 1.01/1.20      inference('sup-', [status(thm)], ['69', '74'])).
% 1.01/1.20  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('77', plain,
% 1.01/1.20      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))
% 1.01/1.20         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['75', '76'])).
% 1.01/1.20  thf('78', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['70', '71'])).
% 1.01/1.20  thf('79', plain,
% 1.01/1.20      (![X8 : $i, X9 : $i]:
% 1.01/1.20         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 1.01/1.20          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 1.01/1.20      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.01/1.20  thf('80', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.01/1.20           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['78', '79'])).
% 1.01/1.20  thf('81', plain,
% 1.01/1.20      ((((k1_tops_1 @ sk_A @ sk_D)
% 1.01/1.20          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.01/1.20             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('demod', [status(thm)], ['53', '77', '80'])).
% 1.01/1.20  thf('82', plain,
% 1.01/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)], ['35', '25', '36'])).
% 1.01/1.20  thf('83', plain,
% 1.01/1.20      (((k1_tops_1 @ sk_A @ sk_D)
% 1.01/1.20         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.01/1.20            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['81', '82'])).
% 1.01/1.20  thf('84', plain,
% 1.01/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('split', [status(esa)], ['29'])).
% 1.01/1.20  thf(involutiveness_k3_subset_1, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.01/1.20       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.01/1.20  thf('85', plain,
% 1.01/1.20      (![X10 : $i, X11 : $i]:
% 1.01/1.20         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 1.01/1.20          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.01/1.20      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.01/1.20  thf('86', plain,
% 1.01/1.20      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.01/1.20          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['84', '85'])).
% 1.01/1.20  thf('87', plain,
% 1.01/1.20      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 1.01/1.20          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['50', '51'])).
% 1.01/1.20  thf('88', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.01/1.20           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['78', '79'])).
% 1.01/1.20  thf('89', plain,
% 1.01/1.20      ((((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.01/1.20          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 1.01/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.20      inference('demod', [status(thm)], ['86', '87', '88'])).
% 1.01/1.20  thf('90', plain,
% 1.01/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)], ['35', '25', '36'])).
% 1.01/1.20  thf('91', plain,
% 1.01/1.20      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.01/1.20         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D))),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['89', '90'])).
% 1.01/1.20  thf('92', plain, (((k1_tops_1 @ sk_A @ sk_D) = (sk_D))),
% 1.01/1.20      inference('sup+', [status(thm)], ['83', '91'])).
% 1.01/1.20  thf('93', plain, ((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C))),
% 1.01/1.20      inference('demod', [status(thm)], ['45', '92'])).
% 1.01/1.20  thf('94', plain,
% 1.01/1.20      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 1.01/1.20      inference('split', [status(esa)], ['3'])).
% 1.01/1.20  thf(l1_zfmisc_1, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.01/1.20  thf('95', plain,
% 1.01/1.20      (![X5 : $i, X7 : $i]:
% 1.01/1.20         ((r1_tarski @ (k1_tarski @ X5) @ X7) | ~ (r2_hidden @ X5 @ X7))),
% 1.01/1.20      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.01/1.20  thf('96', plain,
% 1.01/1.20      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_D))
% 1.01/1.20         <= (((r2_hidden @ sk_B @ sk_D)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['94', '95'])).
% 1.01/1.20  thf(t1_xboole_1, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i]:
% 1.01/1.20     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.01/1.20       ( r1_tarski @ A @ C ) ))).
% 1.01/1.20  thf('97', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         (~ (r1_tarski @ X0 @ X1)
% 1.01/1.20          | ~ (r1_tarski @ X1 @ X2)
% 1.01/1.20          | (r1_tarski @ X0 @ X2))),
% 1.01/1.20      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.01/1.20  thf('98', plain,
% 1.01/1.20      ((![X0 : $i]:
% 1.01/1.20          ((r1_tarski @ (k1_tarski @ sk_B) @ X0) | ~ (r1_tarski @ sk_D @ X0)))
% 1.01/1.20         <= (((r2_hidden @ sk_B @ sk_D)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['96', '97'])).
% 1.01/1.20  thf('99', plain,
% 1.01/1.20      (((r2_hidden @ sk_B @ sk_D)) | 
% 1.01/1.20       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.01/1.20      inference('split', [status(esa)], ['3'])).
% 1.01/1.20  thf('100', plain, (((r2_hidden @ sk_B @ sk_D))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)], ['2', '25', '99'])).
% 1.01/1.20  thf('101', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((r1_tarski @ (k1_tarski @ sk_B) @ X0) | ~ (r1_tarski @ sk_D @ X0))),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['98', '100'])).
% 1.01/1.20  thf('102', plain,
% 1.01/1.20      ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))),
% 1.01/1.20      inference('sup-', [status(thm)], ['93', '101'])).
% 1.01/1.20  thf('103', plain,
% 1.01/1.20      (![X5 : $i, X6 : $i]:
% 1.01/1.20         ((r2_hidden @ X5 @ X6) | ~ (r1_tarski @ (k1_tarski @ X5) @ X6))),
% 1.01/1.20      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.01/1.20  thf('104', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 1.01/1.20      inference('sup-', [status(thm)], ['102', '103'])).
% 1.01/1.20  thf('105', plain, ($false), inference('demod', [status(thm)], ['27', '104'])).
% 1.01/1.20  
% 1.01/1.20  % SZS output end Refutation
% 1.01/1.20  
% 1.01/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
