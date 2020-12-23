%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xIj8ryXrIG

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:08 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 258 expanded)
%              Number of leaves         :   31 (  78 expanded)
%              Depth                    :   16
%              Number of atoms          : 1311 (4297 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X30 @ sk_A )
      | ~ ( r1_tarski @ X30 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X30 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X30 ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X26 @ X25 ) @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X21 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('15',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
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
    inference(split,[status(esa)],['6'])).

thf('26',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X30 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) )
   <= ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      & ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X30 @ sk_A )
          | ~ ( r1_tarski @ X30 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X30 ) ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
   <= ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      & ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X30 @ sk_A )
          | ~ ( r1_tarski @ X30 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X30 ) ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,
    ( ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X30 @ sk_A )
          | ~ ( r1_tarski @ X30 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X30 ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','28'])).

thf('30',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['30'])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X24 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('37',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

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

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_pre_topc @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('45',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k1_tops_1 @ X18 @ X17 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_pre_topc @ X18 @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('51',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_D )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('57',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = sk_D )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r1_tarski @ X27 @ X29 )
      | ( r1_tarski @ ( k1_tops_1 @ X28 @ X27 ) @ ( k1_tops_1 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('68',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('70',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_D )
        | ( m1_subset_1 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','71'])).

thf('73',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['33','72'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('74',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('75',plain,
    ( ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      & ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = sk_D )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('79',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('81',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      & ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_D @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','83'])).

thf('85',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','29','31','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xIj8ryXrIG
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 451 iterations in 0.176s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.63  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.63  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.63  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(t54_tops_1, conjecture,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i,C:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.45/0.63             ( ?[D:$i]:
% 0.45/0.63               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.45/0.63                 ( v3_pre_topc @ D @ A ) & 
% 0.45/0.63                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i]:
% 0.45/0.63        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63          ( ![B:$i,C:$i]:
% 0.45/0.63            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.45/0.63                ( ?[D:$i]:
% 0.45/0.63                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.45/0.63                    ( v3_pre_topc @ D @ A ) & 
% 0.45/0.63                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      (((r2_hidden @ sk_B @ sk_D)
% 0.45/0.63        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.45/0.63       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (((r1_tarski @ sk_D @ sk_C)
% 0.45/0.63        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (((r1_tarski @ sk_D @ sk_C)) | 
% 0.45/0.63       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('split', [status(esa)], ['2'])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.45/0.63       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('split', [status(esa)], ['4'])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X30 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63          | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.45/0.63          | ~ (r1_tarski @ X30 @ sk_C)
% 0.45/0.63          | ~ (r2_hidden @ sk_B @ X30)
% 0.45/0.63          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      ((![X30 : $i]:
% 0.45/0.63          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63           | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.45/0.63           | ~ (r1_tarski @ X30 @ sk_C)
% 0.45/0.63           | ~ (r2_hidden @ sk_B @ X30))) | 
% 0.45/0.63       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('split', [status(esa)], ['6'])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t44_tops_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X25 : $i, X26 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.63          | (r1_tarski @ (k1_tops_1 @ X26 @ X25) @ X25)
% 0.45/0.63          | ~ (l1_pre_topc @ X26))),
% 0.45/0.63      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.63  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.45/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(fc9_tops_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.45/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.63       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (![X21 : $i, X22 : $i]:
% 0.45/0.63         (~ (l1_pre_topc @ X21)
% 0.45/0.63          | ~ (v2_pre_topc @ X21)
% 0.45/0.63          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.63          | (v3_pre_topc @ (k1_tops_1 @ X21 @ X22) @ X21))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.45/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.63  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('18', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.45/0.63         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(dt_k1_tops_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( l1_pre_topc @ A ) & 
% 0.45/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.63       ( m1_subset_1 @
% 0.45/0.63         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (![X19 : $i, X20 : $i]:
% 0.45/0.63         (~ (l1_pre_topc @ X19)
% 0.45/0.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.63          | (m1_subset_1 @ (k1_tops_1 @ X19 @ X20) @ 
% 0.45/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.45/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.63  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.45/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      ((![X30 : $i]:
% 0.45/0.63          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63           | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.45/0.63           | ~ (r1_tarski @ X30 @ sk_C)
% 0.45/0.63           | ~ (r2_hidden @ sk_B @ X30)))
% 0.45/0.63         <= ((![X30 : $i]:
% 0.45/0.63                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.45/0.63                 | ~ (r1_tarski @ X30 @ sk_C)
% 0.45/0.63                 | ~ (r2_hidden @ sk_B @ X30))))),
% 0.45/0.63      inference('split', [status(esa)], ['6'])).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.45/0.63         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.45/0.63         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.45/0.63         <= ((![X30 : $i]:
% 0.45/0.63                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.45/0.63                 | ~ (r1_tarski @ X30 @ sk_C)
% 0.45/0.63                 | ~ (r2_hidden @ sk_B @ X30))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      (((~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.45/0.63         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)))
% 0.45/0.63         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) & 
% 0.45/0.63             (![X30 : $i]:
% 0.45/0.63                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.45/0.63                 | ~ (r1_tarski @ X30 @ sk_C)
% 0.45/0.63                 | ~ (r2_hidden @ sk_B @ X30))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['19', '26'])).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))
% 0.45/0.63         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) & 
% 0.45/0.63             (![X30 : $i]:
% 0.45/0.63                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.45/0.63                 | ~ (r1_tarski @ X30 @ sk_C)
% 0.45/0.63                 | ~ (r2_hidden @ sk_B @ X30))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['18', '27'])).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      (~
% 0.45/0.63       (![X30 : $i]:
% 0.45/0.63          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63           | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.45/0.63           | ~ (r1_tarski @ X30 @ sk_C)
% 0.45/0.63           | ~ (r2_hidden @ sk_B @ X30))) | 
% 0.45/0.63       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['12', '28'])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      (((v3_pre_topc @ sk_D @ sk_A)
% 0.45/0.63        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.45/0.63       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('split', [status(esa)], ['30'])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.45/0.63      inference('split', [status(esa)], ['30'])).
% 0.45/0.63  thf('35', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('split', [status(esa)], ['4'])).
% 0.45/0.63  thf(t30_tops_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.63             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      (![X23 : $i, X24 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.45/0.63          | ~ (v3_pre_topc @ X23 @ X24)
% 0.45/0.63          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 0.45/0.63          | ~ (l1_pre_topc @ X24))),
% 0.45/0.63      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      (((~ (l1_pre_topc @ sk_A)
% 0.45/0.63         | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.45/0.63         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.63  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      ((((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.45/0.63         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A))
% 0.45/0.63         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['34', '39'])).
% 0.45/0.63  thf('41', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('split', [status(esa)], ['4'])).
% 0.45/0.63  thf(dt_k3_subset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.63  thf('42', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.45/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      (((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.45/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.63  thf(t52_pre_topc, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.45/0.63             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.45/0.63               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.45/0.63  thf('44', plain,
% 0.45/0.63      (![X15 : $i, X16 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.45/0.63          | ~ (v4_pre_topc @ X15 @ X16)
% 0.45/0.63          | ((k2_pre_topc @ X16 @ X15) = (X15))
% 0.45/0.63          | ~ (l1_pre_topc @ X16))),
% 0.45/0.63      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.45/0.63  thf('45', plain,
% 0.45/0.63      (((~ (l1_pre_topc @ sk_A)
% 0.45/0.63         | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.45/0.63             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.45/0.63         | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.63  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('47', plain,
% 0.45/0.63      (((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.45/0.63           = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.45/0.63         | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.63  thf('48', plain,
% 0.45/0.63      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.45/0.63          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.45/0.63         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['40', '47'])).
% 0.45/0.63  thf('49', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('split', [status(esa)], ['4'])).
% 0.45/0.63  thf(d1_tops_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( k1_tops_1 @ A @ B ) =
% 0.45/0.63             ( k3_subset_1 @
% 0.45/0.63               ( u1_struct_0 @ A ) @ 
% 0.45/0.63               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.45/0.63  thf('50', plain,
% 0.45/0.63      (![X17 : $i, X18 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.45/0.63          | ((k1_tops_1 @ X18 @ X17)
% 0.45/0.63              = (k3_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.45/0.63                 (k2_pre_topc @ X18 @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X17))))
% 0.45/0.63          | ~ (l1_pre_topc @ X18))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.45/0.63  thf('51', plain,
% 0.45/0.63      (((~ (l1_pre_topc @ sk_A)
% 0.45/0.63         | ((k1_tops_1 @ sk_A @ sk_D)
% 0.45/0.63             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.63                (k2_pre_topc @ sk_A @ 
% 0.45/0.63                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.63  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('53', plain,
% 0.45/0.63      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.45/0.63          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.63             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.63  thf('54', plain,
% 0.45/0.63      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.45/0.63          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.63             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))
% 0.45/0.63         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['48', '53'])).
% 0.45/0.63  thf('55', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('split', [status(esa)], ['4'])).
% 0.45/0.63  thf(involutiveness_k3_subset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.45/0.63  thf('56', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]:
% 0.45/0.63         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.45/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.45/0.63      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.45/0.63  thf('57', plain,
% 0.45/0.63      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.63          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.63  thf('58', plain,
% 0.45/0.63      ((((k1_tops_1 @ sk_A @ sk_D) = (sk_D)))
% 0.45/0.63         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['54', '57'])).
% 0.45/0.63  thf('59', plain,
% 0.45/0.63      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.45/0.63      inference('split', [status(esa)], ['2'])).
% 0.45/0.63  thf('60', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('61', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('split', [status(esa)], ['4'])).
% 0.45/0.63  thf(t48_tops_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63               ( ( r1_tarski @ B @ C ) =>
% 0.45/0.63                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('62', plain,
% 0.45/0.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.45/0.63          | ~ (r1_tarski @ X27 @ X29)
% 0.45/0.63          | (r1_tarski @ (k1_tops_1 @ X28 @ X27) @ (k1_tops_1 @ X28 @ X29))
% 0.45/0.63          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.45/0.63          | ~ (l1_pre_topc @ X28))),
% 0.45/0.63      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.45/0.63  thf('63', plain,
% 0.45/0.63      ((![X0 : $i]:
% 0.45/0.63          (~ (l1_pre_topc @ sk_A)
% 0.45/0.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.45/0.63           | ~ (r1_tarski @ sk_D @ X0)))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['61', '62'])).
% 0.45/0.63  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('65', plain,
% 0.45/0.63      ((![X0 : $i]:
% 0.45/0.63          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.45/0.63           | ~ (r1_tarski @ sk_D @ X0)))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('demod', [status(thm)], ['63', '64'])).
% 0.45/0.63  thf('66', plain,
% 0.45/0.63      (((~ (r1_tarski @ sk_D @ sk_C)
% 0.45/0.63         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.45/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['60', '65'])).
% 0.45/0.63  thf('67', plain,
% 0.45/0.63      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.45/0.63         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['59', '66'])).
% 0.45/0.63  thf(t3_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.63  thf('68', plain,
% 0.45/0.63      (![X6 : $i, X8 : $i]:
% 0.45/0.63         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('69', plain,
% 0.45/0.63      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 0.45/0.63         (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.45/0.63         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.45/0.63  thf(t4_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.45/0.63       ( m1_subset_1 @ A @ C ) ))).
% 0.45/0.63  thf('70', plain,
% 0.45/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X9 @ X10)
% 0.45/0.63          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.45/0.63          | (m1_subset_1 @ X9 @ X11))),
% 0.45/0.63      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.63  thf('71', plain,
% 0.45/0.63      ((![X0 : $i]:
% 0.45/0.63          ((m1_subset_1 @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.45/0.63           | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))))
% 0.45/0.63         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.63  thf('72', plain,
% 0.45/0.63      ((![X0 : $i]:
% 0.45/0.63          (~ (r2_hidden @ X0 @ sk_D)
% 0.45/0.63           | (m1_subset_1 @ X0 @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.45/0.63         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.63             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['58', '71'])).
% 0.45/0.63  thf('73', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.45/0.63         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.45/0.63             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.63             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['33', '72'])).
% 0.45/0.63  thf(t2_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.63       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.63  thf('74', plain,
% 0.45/0.63      (![X4 : $i, X5 : $i]:
% 0.45/0.63         ((r2_hidden @ X4 @ X5)
% 0.45/0.63          | (v1_xboole_0 @ X5)
% 0.45/0.63          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.63  thf('75', plain,
% 0.45/0.63      ((((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.45/0.63         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.45/0.63         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.45/0.63             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.63             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['73', '74'])).
% 0.45/0.63  thf('76', plain,
% 0.45/0.63      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.45/0.63         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.45/0.63      inference('split', [status(esa)], ['6'])).
% 0.45/0.63  thf('77', plain,
% 0.45/0.63      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.45/0.63         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) & 
% 0.45/0.63             ((r2_hidden @ sk_B @ sk_D)) & 
% 0.45/0.63             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.63             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['75', '76'])).
% 0.45/0.63  thf('78', plain,
% 0.45/0.63      ((((k1_tops_1 @ sk_A @ sk_D) = (sk_D)))
% 0.45/0.63         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['54', '57'])).
% 0.45/0.63  thf('79', plain,
% 0.45/0.63      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 0.45/0.63         (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.45/0.63         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.45/0.63  thf('80', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.45/0.63         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.63             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['78', '79'])).
% 0.45/0.63  thf(t5_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.45/0.63          ( v1_xboole_0 @ C ) ) ))).
% 0.45/0.63  thf('81', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X12 @ X13)
% 0.45/0.63          | ~ (v1_xboole_0 @ X14)
% 0.45/0.63          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.63  thf('82', plain,
% 0.45/0.63      ((![X0 : $i]:
% 0.45/0.63          (~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.45/0.63           | ~ (r2_hidden @ X0 @ sk_D)))
% 0.45/0.63         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.63             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['80', '81'])).
% 0.45/0.63  thf('83', plain,
% 0.45/0.63      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D))
% 0.45/0.63         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) & 
% 0.45/0.63             ((r2_hidden @ sk_B @ sk_D)) & 
% 0.45/0.63             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.63             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['77', '82'])).
% 0.45/0.63  thf('84', plain,
% 0.45/0.63      (~ ((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.45/0.63       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.45/0.63       ~ ((r1_tarski @ sk_D @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_D)) | 
% 0.45/0.63       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['32', '83'])).
% 0.45/0.63  thf('85', plain, ($false),
% 0.45/0.63      inference('sat_resolution*', [status(thm)],
% 0.45/0.63                ['1', '3', '5', '7', '29', '31', '84'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
