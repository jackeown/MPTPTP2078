%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RSqd7Vj75K

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:07 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 631 expanded)
%              Number of leaves         :   34 ( 180 expanded)
%              Depth                    :   19
%              Number of atoms          : 1268 (10456 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X32 @ sk_A )
      | ~ ( r1_tarski @ X32 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X32 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X32 @ sk_A )
        | ~ ( r1_tarski @ X32 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X32 ) )
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
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
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
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X32 @ sk_A )
      | ~ ( r1_tarski @ X32 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X32 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X32 @ sk_A )
        | ~ ( r1_tarski @ X32 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X32 ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X32 @ sk_A )
        | ~ ( r1_tarski @ X32 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X32 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X32 @ sk_A )
        | ~ ( r1_tarski @ X32 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X32 ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X28 @ X27 ) @ X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X23 @ X24 ) @ X23 ) ) ),
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
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X32 @ sk_A )
        | ~ ( r1_tarski @ X32 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X32 ) ) ),
    inference(demod,[status(thm)],['12','17','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X32 @ sk_A )
          | ~ ( r1_tarski @ X32 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X32 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( r1_tarski @ X29 @ X31 )
      | ( r1_tarski @ ( k1_tops_1 @ X30 @ X29 ) @ ( k1_tops_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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
    | ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X32 @ sk_A )
        | ~ ( r1_tarski @ X32 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X32 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k1_tops_1 @ X20 @ X19 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k2_pre_topc @ X20 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['35','25','36'])).

thf('55',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simpl_trail,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('57',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X26 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 ) @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('58',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('61',plain,
    ( ( ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['62'])).

thf('65',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','25','64'])).

thf('66',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['63','65'])).

thf('67',plain,
    ( ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['35','25','36'])).

thf('69',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['67','68'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('70',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('71',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['55','77','80'])).

thf('82',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','36'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('85',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('86',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','36'])).

thf('89',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('91',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['86','89','90'])).

thf('92',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = sk_D ),
    inference('sup+',[status(thm)],['81','91'])).

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
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X7 ) @ X9 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('96',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('97',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('98',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_D )
      = sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D @ X0 )
        | ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('102',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['2','25','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_D @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['100','102'])).

thf('104',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['93','103'])).

thf('105',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k1_tarski @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('106',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['27','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RSqd7Vj75K
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:00:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.76/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.96  % Solved by: fo/fo7.sh
% 0.76/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.96  % done 1159 iterations in 0.506s
% 0.76/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.96  % SZS output start Refutation
% 0.76/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.96  thf(sk_D_type, type, sk_D: $i).
% 0.76/0.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.96  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.76/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.96  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.76/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.96  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/0.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.96  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.76/0.96  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.76/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.96  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.76/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.96  thf(t54_tops_1, conjecture,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.96       ( ![B:$i,C:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.76/0.96             ( ?[D:$i]:
% 0.76/0.96               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.76/0.96                 ( v3_pre_topc @ D @ A ) & 
% 0.76/0.96                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.96    (~( ![A:$i]:
% 0.76/0.96        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.96          ( ![B:$i,C:$i]:
% 0.76/0.96            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.76/0.96                ( ?[D:$i]:
% 0.76/0.96                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.76/0.96                    ( v3_pre_topc @ D @ A ) & 
% 0.76/0.96                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.76/0.96    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 0.76/0.96  thf('0', plain,
% 0.76/0.96      (![X32 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96          | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.76/0.96          | ~ (r1_tarski @ X32 @ sk_C)
% 0.76/0.96          | ~ (r2_hidden @ sk_B @ X32)
% 0.76/0.96          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('1', plain,
% 0.76/0.96      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.76/0.96         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.76/0.96      inference('split', [status(esa)], ['0'])).
% 0.76/0.96  thf('2', plain,
% 0.76/0.96      ((![X32 : $i]:
% 0.76/0.96          (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96           | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.76/0.96           | ~ (r1_tarski @ X32 @ sk_C)
% 0.76/0.96           | ~ (r2_hidden @ sk_B @ X32))) | 
% 0.76/0.96       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.76/0.96      inference('split', [status(esa)], ['0'])).
% 0.76/0.96  thf('3', plain,
% 0.76/0.96      (((r2_hidden @ sk_B @ sk_D)
% 0.76/0.96        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('4', plain,
% 0.76/0.96      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.76/0.96         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.76/0.96      inference('split', [status(esa)], ['3'])).
% 0.76/0.96  thf('5', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(dt_k1_tops_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( ( l1_pre_topc @ A ) & 
% 0.76/0.96         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.76/0.96       ( m1_subset_1 @
% 0.76/0.96         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.76/0.96  thf('6', plain,
% 0.76/0.96      (![X21 : $i, X22 : $i]:
% 0.76/0.96         (~ (l1_pre_topc @ X21)
% 0.76/0.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.76/0.96          | (m1_subset_1 @ (k1_tops_1 @ X21 @ X22) @ 
% 0.76/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 0.76/0.96      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.76/0.96  thf('7', plain,
% 0.76/0.96      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.76/0.96         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96        | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['5', '6'])).
% 0.76/0.96  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('9', plain,
% 0.76/0.96      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.76/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('demod', [status(thm)], ['7', '8'])).
% 0.76/0.96  thf('10', plain,
% 0.76/0.96      (![X32 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96          | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.76/0.96          | ~ (r1_tarski @ X32 @ sk_C)
% 0.76/0.96          | ~ (r2_hidden @ sk_B @ X32)
% 0.76/0.96          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('11', plain,
% 0.76/0.96      ((![X32 : $i]:
% 0.76/0.96          (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96           | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.76/0.96           | ~ (r1_tarski @ X32 @ sk_C)
% 0.76/0.96           | ~ (r2_hidden @ sk_B @ X32)))
% 0.76/0.96         <= ((![X32 : $i]:
% 0.76/0.97                (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97                 | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.76/0.97                 | ~ (r1_tarski @ X32 @ sk_C)
% 0.76/0.97                 | ~ (r2_hidden @ sk_B @ X32))))),
% 0.76/0.97      inference('split', [status(esa)], ['10'])).
% 0.76/0.97  thf('12', plain,
% 0.76/0.97      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.76/0.97         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.76/0.97         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.76/0.97         <= ((![X32 : $i]:
% 0.76/0.97                (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97                 | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.76/0.97                 | ~ (r1_tarski @ X32 @ sk_C)
% 0.76/0.97                 | ~ (r2_hidden @ sk_B @ X32))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['9', '11'])).
% 0.76/0.97  thf('13', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(t44_tops_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( l1_pre_topc @ A ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.76/0.97  thf('14', plain,
% 0.76/0.97      (![X27 : $i, X28 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.76/0.97          | (r1_tarski @ (k1_tops_1 @ X28 @ X27) @ X27)
% 0.76/0.97          | ~ (l1_pre_topc @ X28))),
% 0.76/0.97      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.76/0.97  thf('15', plain,
% 0.76/0.97      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.76/0.97      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.97  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('17', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.76/0.97      inference('demod', [status(thm)], ['15', '16'])).
% 0.76/0.97  thf('18', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(fc9_tops_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.76/0.97         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.76/0.97       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.76/0.97  thf('19', plain,
% 0.76/0.97      (![X23 : $i, X24 : $i]:
% 0.76/0.97         (~ (l1_pre_topc @ X23)
% 0.76/0.97          | ~ (v2_pre_topc @ X23)
% 0.76/0.97          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.76/0.97          | (v3_pre_topc @ (k1_tops_1 @ X23 @ X24) @ X23))),
% 0.76/0.97      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.76/0.97  thf('20', plain,
% 0.76/0.97      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.76/0.97        | ~ (v2_pre_topc @ sk_A)
% 0.76/0.97        | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.97  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('23', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.76/0.97      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.76/0.97  thf('24', plain,
% 0.76/0.97      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.76/0.97         <= ((![X32 : $i]:
% 0.76/0.97                (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97                 | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.76/0.97                 | ~ (r1_tarski @ X32 @ sk_C)
% 0.76/0.97                 | ~ (r2_hidden @ sk_B @ X32))))),
% 0.76/0.97      inference('demod', [status(thm)], ['12', '17', '23'])).
% 0.76/0.97  thf('25', plain,
% 0.76/0.97      (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) | 
% 0.76/0.97       ~
% 0.76/0.97       (![X32 : $i]:
% 0.76/0.97          (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97           | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.76/0.97           | ~ (r1_tarski @ X32 @ sk_C)
% 0.76/0.97           | ~ (r2_hidden @ sk_B @ X32)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['4', '24'])).
% 0.76/0.97  thf('26', plain, (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.76/0.97      inference('sat_resolution*', [status(thm)], ['2', '25'])).
% 0.76/0.97  thf('27', plain, (~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.76/0.97      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.76/0.97  thf('28', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('29', plain,
% 0.76/0.97      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('30', plain,
% 0.76/0.97      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('split', [status(esa)], ['29'])).
% 0.76/0.97  thf(t48_tops_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( l1_pre_topc @ A ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97           ( ![C:$i]:
% 0.76/0.97             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97               ( ( r1_tarski @ B @ C ) =>
% 0.76/0.97                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.76/0.97  thf('31', plain,
% 0.76/0.97      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.76/0.97          | ~ (r1_tarski @ X29 @ X31)
% 0.76/0.97          | (r1_tarski @ (k1_tops_1 @ X30 @ X29) @ (k1_tops_1 @ X30 @ X31))
% 0.76/0.97          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.76/0.97          | ~ (l1_pre_topc @ X30))),
% 0.76/0.97      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.76/0.97  thf('32', plain,
% 0.76/0.97      ((![X0 : $i]:
% 0.76/0.97          (~ (l1_pre_topc @ sk_A)
% 0.76/0.97           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.76/0.97           | ~ (r1_tarski @ sk_D @ X0)))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['30', '31'])).
% 0.76/0.97  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('34', plain,
% 0.76/0.97      ((![X0 : $i]:
% 0.76/0.97          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.76/0.97           | ~ (r1_tarski @ sk_D @ X0)))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('demod', [status(thm)], ['32', '33'])).
% 0.76/0.97  thf('35', plain,
% 0.76/0.97      (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) | 
% 0.76/0.97       (![X32 : $i]:
% 0.76/0.97          (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97           | ~ (v3_pre_topc @ X32 @ sk_A)
% 0.76/0.97           | ~ (r1_tarski @ X32 @ sk_C)
% 0.76/0.97           | ~ (r2_hidden @ sk_B @ X32)))),
% 0.76/0.97      inference('split', [status(esa)], ['0'])).
% 0.76/0.97  thf('36', plain,
% 0.76/0.97      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.76/0.97       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.76/0.97      inference('split', [status(esa)], ['29'])).
% 0.76/0.97  thf('37', plain,
% 0.76/0.97      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.76/0.97      inference('sat_resolution*', [status(thm)], ['35', '25', '36'])).
% 0.76/0.97  thf('38', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.76/0.97          | ~ (r1_tarski @ sk_D @ X0))),
% 0.76/0.97      inference('simpl_trail', [status(thm)], ['34', '37'])).
% 0.76/0.97  thf('39', plain,
% 0.76/0.97      ((~ (r1_tarski @ sk_D @ sk_C)
% 0.76/0.97        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['28', '38'])).
% 0.76/0.97  thf('40', plain,
% 0.76/0.97      (((r1_tarski @ sk_D @ sk_C)
% 0.76/0.97        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('41', plain,
% 0.76/0.97      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.76/0.97      inference('split', [status(esa)], ['40'])).
% 0.76/0.97  thf('42', plain,
% 0.76/0.97      (((r1_tarski @ sk_D @ sk_C)) | 
% 0.76/0.97       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.76/0.97      inference('split', [status(esa)], ['40'])).
% 0.76/0.97  thf('43', plain, (((r1_tarski @ sk_D @ sk_C))),
% 0.76/0.97      inference('sat_resolution*', [status(thm)], ['2', '25', '42'])).
% 0.76/0.97  thf('44', plain, ((r1_tarski @ sk_D @ sk_C)),
% 0.76/0.97      inference('simpl_trail', [status(thm)], ['41', '43'])).
% 0.76/0.97  thf('45', plain,
% 0.76/0.97      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.76/0.97      inference('demod', [status(thm)], ['39', '44'])).
% 0.76/0.97  thf('46', plain,
% 0.76/0.97      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('split', [status(esa)], ['29'])).
% 0.76/0.97  thf(d1_tops_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( l1_pre_topc @ A ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97           ( ( k1_tops_1 @ A @ B ) =
% 0.76/0.97             ( k3_subset_1 @
% 0.76/0.97               ( u1_struct_0 @ A ) @ 
% 0.76/0.97               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.76/0.97  thf('47', plain,
% 0.76/0.97      (![X19 : $i, X20 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.76/0.97          | ((k1_tops_1 @ X20 @ X19)
% 0.76/0.97              = (k3_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.76/0.97                 (k2_pre_topc @ X20 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19))))
% 0.76/0.97          | ~ (l1_pre_topc @ X20))),
% 0.76/0.97      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.76/0.97  thf('48', plain,
% 0.76/0.97      (((~ (l1_pre_topc @ sk_A)
% 0.76/0.97         | ((k1_tops_1 @ sk_A @ sk_D)
% 0.76/0.97             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.97                (k2_pre_topc @ sk_A @ 
% 0.76/0.97                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['46', '47'])).
% 0.76/0.97  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('50', plain,
% 0.76/0.97      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('split', [status(esa)], ['29'])).
% 0.76/0.97  thf(d5_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.76/0.97  thf('51', plain,
% 0.76/0.97      (![X10 : $i, X11 : $i]:
% 0.76/0.97         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.76/0.97          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.76/0.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.76/0.97  thf('52', plain,
% 0.76/0.97      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 0.76/0.97          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['50', '51'])).
% 0.76/0.97  thf('53', plain,
% 0.76/0.97      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.76/0.97          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.97             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('demod', [status(thm)], ['48', '49', '52'])).
% 0.76/0.97  thf('54', plain,
% 0.76/0.97      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.76/0.97      inference('sat_resolution*', [status(thm)], ['35', '25', '36'])).
% 0.76/0.97  thf('55', plain,
% 0.76/0.97      (((k1_tops_1 @ sk_A @ sk_D)
% 0.76/0.97         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.97            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.76/0.97      inference('simpl_trail', [status(thm)], ['53', '54'])).
% 0.76/0.97  thf('56', plain,
% 0.76/0.97      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('split', [status(esa)], ['29'])).
% 0.76/0.97  thf(t30_tops_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( l1_pre_topc @ A ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97           ( ( v3_pre_topc @ B @ A ) <=>
% 0.76/0.97             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.76/0.97  thf('57', plain,
% 0.76/0.97      (![X25 : $i, X26 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.76/0.97          | ~ (v3_pre_topc @ X25 @ X26)
% 0.76/0.97          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X26) @ X25) @ X26)
% 0.76/0.97          | ~ (l1_pre_topc @ X26))),
% 0.76/0.97      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.76/0.97  thf('58', plain,
% 0.76/0.97      (((~ (l1_pre_topc @ sk_A)
% 0.76/0.97         | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.76/0.97         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['56', '57'])).
% 0.76/0.97  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('60', plain,
% 0.76/0.97      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 0.76/0.97          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['50', '51'])).
% 0.76/0.97  thf('61', plain,
% 0.76/0.97      ((((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.76/0.97         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.76/0.97  thf('62', plain,
% 0.76/0.97      (((v3_pre_topc @ sk_D @ sk_A)
% 0.76/0.97        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('63', plain,
% 0.76/0.97      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.76/0.97      inference('split', [status(esa)], ['62'])).
% 0.76/0.97  thf('64', plain,
% 0.76/0.97      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.76/0.97       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.76/0.97      inference('split', [status(esa)], ['62'])).
% 0.76/0.97  thf('65', plain, (((v3_pre_topc @ sk_D @ sk_A))),
% 0.76/0.97      inference('sat_resolution*', [status(thm)], ['2', '25', '64'])).
% 0.76/0.97  thf('66', plain, ((v3_pre_topc @ sk_D @ sk_A)),
% 0.76/0.97      inference('simpl_trail', [status(thm)], ['63', '65'])).
% 0.76/0.97  thf('67', plain,
% 0.76/0.97      (((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('demod', [status(thm)], ['61', '66'])).
% 0.76/0.97  thf('68', plain,
% 0.76/0.97      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.76/0.97      inference('sat_resolution*', [status(thm)], ['35', '25', '36'])).
% 0.76/0.97  thf('69', plain,
% 0.76/0.97      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)),
% 0.76/0.97      inference('simpl_trail', [status(thm)], ['67', '68'])).
% 0.76/0.97  thf(t36_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.76/0.97  thf('70', plain,
% 0.76/0.97      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.76/0.97      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.76/0.97  thf(t3_subset, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.97  thf('71', plain,
% 0.76/0.97      (![X14 : $i, X16 : $i]:
% 0.76/0.97         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.97  thf('72', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['70', '71'])).
% 0.76/0.97  thf(t52_pre_topc, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( l1_pre_topc @ A ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.76/0.97             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.76/0.97               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.76/0.97  thf('73', plain,
% 0.76/0.97      (![X17 : $i, X18 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.76/0.97          | ~ (v4_pre_topc @ X17 @ X18)
% 0.76/0.97          | ((k2_pre_topc @ X18 @ X17) = (X17))
% 0.76/0.97          | ~ (l1_pre_topc @ X18))),
% 0.76/0.97      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.76/0.97  thf('74', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (~ (l1_pre_topc @ X0)
% 0.76/0.97          | ((k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.76/0.97              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.76/0.97          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['72', '73'])).
% 0.76/0.97  thf('75', plain,
% 0.76/0.97      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.76/0.97          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.76/0.97        | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['69', '74'])).
% 0.76/0.97  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('77', plain,
% 0.76/0.97      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.76/0.97         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))),
% 0.76/0.97      inference('demod', [status(thm)], ['75', '76'])).
% 0.76/0.97  thf('78', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['70', '71'])).
% 0.76/0.97  thf('79', plain,
% 0.76/0.97      (![X10 : $i, X11 : $i]:
% 0.76/0.97         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.76/0.97          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.76/0.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.76/0.97  thf('80', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.76/0.97           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['78', '79'])).
% 0.76/0.97  thf('81', plain,
% 0.76/0.97      (((k1_tops_1 @ sk_A @ sk_D)
% 0.76/0.97         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.97            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.76/0.97      inference('demod', [status(thm)], ['55', '77', '80'])).
% 0.76/0.97  thf('82', plain,
% 0.76/0.97      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('split', [status(esa)], ['29'])).
% 0.76/0.97  thf('83', plain,
% 0.76/0.97      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.76/0.97      inference('sat_resolution*', [status(thm)], ['2', '25', '36'])).
% 0.76/0.97  thf('84', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('simpl_trail', [status(thm)], ['82', '83'])).
% 0.76/0.97  thf(involutiveness_k3_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.76/0.97  thf('85', plain,
% 0.76/0.97      (![X12 : $i, X13 : $i]:
% 0.76/0.97         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 0.76/0.97          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.76/0.97      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.76/0.97  thf('86', plain,
% 0.76/0.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.97         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D))),
% 0.76/0.97      inference('sup-', [status(thm)], ['84', '85'])).
% 0.76/0.97  thf('87', plain,
% 0.76/0.97      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 0.76/0.97          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.76/0.97         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['50', '51'])).
% 0.76/0.97  thf('88', plain,
% 0.76/0.97      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.76/0.97      inference('sat_resolution*', [status(thm)], ['2', '25', '36'])).
% 0.76/0.97  thf('89', plain,
% 0.76/0.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 0.76/0.97         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))),
% 0.76/0.97      inference('simpl_trail', [status(thm)], ['87', '88'])).
% 0.76/0.97  thf('90', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.76/0.97           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['78', '79'])).
% 0.76/0.97  thf('91', plain,
% 0.76/0.97      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.97         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D))),
% 0.76/0.97      inference('demod', [status(thm)], ['86', '89', '90'])).
% 0.76/0.97  thf('92', plain, (((k1_tops_1 @ sk_A @ sk_D) = (sk_D))),
% 0.76/0.97      inference('sup+', [status(thm)], ['81', '91'])).
% 0.76/0.97  thf('93', plain, ((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.76/0.97      inference('demod', [status(thm)], ['45', '92'])).
% 0.76/0.97  thf('94', plain,
% 0.76/0.97      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.76/0.97      inference('split', [status(esa)], ['3'])).
% 0.76/0.97  thf(l1_zfmisc_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.76/0.97  thf('95', plain,
% 0.76/0.97      (![X7 : $i, X9 : $i]:
% 0.76/0.97         ((r1_tarski @ (k1_tarski @ X7) @ X9) | ~ (r2_hidden @ X7 @ X9))),
% 0.76/0.97      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.76/0.97  thf('96', plain,
% 0.76/0.97      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_D))
% 0.76/0.97         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['94', '95'])).
% 0.76/0.97  thf(t12_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.76/0.97  thf('97', plain,
% 0.76/0.97      (![X3 : $i, X4 : $i]:
% 0.76/0.97         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.76/0.97      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.97  thf('98', plain,
% 0.76/0.97      ((((k2_xboole_0 @ (k1_tarski @ sk_B) @ sk_D) = (sk_D)))
% 0.76/0.97         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['96', '97'])).
% 0.76/0.97  thf(t11_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.76/0.97  thf('99', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.76/0.97  thf('100', plain,
% 0.76/0.97      ((![X0 : $i]:
% 0.76/0.97          (~ (r1_tarski @ sk_D @ X0) | (r1_tarski @ (k1_tarski @ sk_B) @ X0)))
% 0.76/0.97         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['98', '99'])).
% 0.76/0.97  thf('101', plain,
% 0.76/0.97      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.76/0.97       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.76/0.97      inference('split', [status(esa)], ['3'])).
% 0.76/0.97  thf('102', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.76/0.97      inference('sat_resolution*', [status(thm)], ['2', '25', '101'])).
% 0.76/0.97  thf('103', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (r1_tarski @ sk_D @ X0) | (r1_tarski @ (k1_tarski @ sk_B) @ X0))),
% 0.76/0.97      inference('simpl_trail', [status(thm)], ['100', '102'])).
% 0.76/0.97  thf('104', plain,
% 0.76/0.97      ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.76/0.97      inference('sup-', [status(thm)], ['93', '103'])).
% 0.76/0.97  thf('105', plain,
% 0.76/0.97      (![X7 : $i, X8 : $i]:
% 0.76/0.97         ((r2_hidden @ X7 @ X8) | ~ (r1_tarski @ (k1_tarski @ X7) @ X8))),
% 0.76/0.97      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.76/0.97  thf('106', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.76/0.97      inference('sup-', [status(thm)], ['104', '105'])).
% 0.76/0.97  thf('107', plain, ($false), inference('demod', [status(thm)], ['27', '106'])).
% 0.76/0.97  
% 0.76/0.97  % SZS output end Refutation
% 0.76/0.97  
% 0.76/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
