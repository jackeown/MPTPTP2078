%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q0wT3c3LSC

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:06 EST 2020

% Result     : Theorem 15.46s
% Output     : Refutation 15.46s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 207 expanded)
%              Number of leaves         :   34 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          : 1295 (3034 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X35: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X35 @ sk_A )
      | ~ ( r1_tarski @ X35 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X35 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X35 @ sk_A )
        | ~ ( r1_tarski @ X35 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X35 ) )
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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X31 @ X30 ) @ X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X26 @ X27 ) @ X26 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
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
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X35 @ sk_A )
        | ~ ( r1_tarski @ X35 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X35 ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X35 @ sk_A )
        | ~ ( r1_tarski @ X35 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X35 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('26',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X35 @ sk_A )
        | ~ ( r1_tarski @ X35 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X35 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) )
   <= ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X35 @ sk_A )
          | ~ ( r1_tarski @ X35 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
   <= ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X35 @ sk_A )
          | ~ ( r1_tarski @ X35 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,
    ( ~ ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X35 @ sk_A )
          | ~ ( r1_tarski @ X35 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X35 ) )
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
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['30'])).

thf('33',plain,
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

thf('34',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X29 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('35',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

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

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v4_pre_topc @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ X20 )
        = X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('43',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,
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

thf('48',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k1_tops_1 @ X23 @ X22 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k2_pre_topc @ X23 @ ( k3_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 ) ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('49',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_D )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X19 @ ( k3_subset_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('55',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = sk_D )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
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

thf('60',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( r1_tarski @ X32 @ X34 )
      | ( r1_tarski @ ( k1_tops_1 @ X33 @ X32 ) @ ( k1_tops_1 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('67',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k2_xboole_0 @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['56','67'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('69',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['70'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('72',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('74',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('82',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('83',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('85',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_D ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k1_tarski @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('87',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_B @ ( k2_xboole_0 @ X0 @ sk_D ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['80','87'])).

thf('89',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['68','88'])).

thf('90',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('91',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_D @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','29','31','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q0wT3c3LSC
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:41:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 15.46/15.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 15.46/15.67  % Solved by: fo/fo7.sh
% 15.46/15.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.46/15.67  % done 16326 iterations in 15.209s
% 15.46/15.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 15.46/15.67  % SZS output start Refutation
% 15.46/15.67  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 15.46/15.67  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 15.46/15.67  thf(sk_D_type, type, sk_D: $i).
% 15.46/15.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.46/15.67  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 15.46/15.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 15.46/15.67  thf(sk_A_type, type, sk_A: $i).
% 15.46/15.67  thf(sk_B_type, type, sk_B: $i).
% 15.46/15.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 15.46/15.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 15.46/15.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.46/15.67  thf(sk_C_type, type, sk_C: $i).
% 15.46/15.67  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 15.46/15.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.46/15.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 15.46/15.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 15.46/15.67  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 15.46/15.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 15.46/15.67  thf(t54_tops_1, conjecture,
% 15.46/15.67    (![A:$i]:
% 15.46/15.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 15.46/15.67       ( ![B:$i,C:$i]:
% 15.46/15.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.46/15.67           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 15.46/15.67             ( ?[D:$i]:
% 15.46/15.67               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 15.46/15.67                 ( v3_pre_topc @ D @ A ) & 
% 15.46/15.67                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 15.46/15.67  thf(zf_stmt_0, negated_conjecture,
% 15.46/15.67    (~( ![A:$i]:
% 15.46/15.67        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 15.46/15.67          ( ![B:$i,C:$i]:
% 15.46/15.67            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.46/15.67              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 15.46/15.67                ( ?[D:$i]:
% 15.46/15.67                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 15.46/15.67                    ( v3_pre_topc @ D @ A ) & 
% 15.46/15.67                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 15.46/15.67    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 15.46/15.67  thf('0', plain,
% 15.46/15.67      (((r2_hidden @ sk_B @ sk_D)
% 15.46/15.67        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf('1', plain,
% 15.46/15.67      (((r2_hidden @ sk_B @ sk_D)) | 
% 15.46/15.67       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 15.46/15.67      inference('split', [status(esa)], ['0'])).
% 15.46/15.67  thf('2', plain,
% 15.46/15.67      (((r1_tarski @ sk_D @ sk_C)
% 15.46/15.67        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf('3', plain,
% 15.46/15.67      (((r1_tarski @ sk_D @ sk_C)) | 
% 15.46/15.67       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 15.46/15.67      inference('split', [status(esa)], ['2'])).
% 15.46/15.67  thf('4', plain,
% 15.46/15.67      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.46/15.67        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf('5', plain,
% 15.46/15.67      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 15.46/15.67       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 15.46/15.67      inference('split', [status(esa)], ['4'])).
% 15.46/15.67  thf('6', plain,
% 15.46/15.67      (![X35 : $i]:
% 15.46/15.67         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.46/15.67          | ~ (v3_pre_topc @ X35 @ sk_A)
% 15.46/15.67          | ~ (r1_tarski @ X35 @ sk_C)
% 15.46/15.67          | ~ (r2_hidden @ sk_B @ X35)
% 15.46/15.67          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf('7', plain,
% 15.46/15.67      ((![X35 : $i]:
% 15.46/15.67          (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.46/15.67           | ~ (v3_pre_topc @ X35 @ sk_A)
% 15.46/15.67           | ~ (r1_tarski @ X35 @ sk_C)
% 15.46/15.67           | ~ (r2_hidden @ sk_B @ X35))) | 
% 15.46/15.67       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 15.46/15.67      inference('split', [status(esa)], ['6'])).
% 15.46/15.67  thf('8', plain,
% 15.46/15.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf(t44_tops_1, axiom,
% 15.46/15.67    (![A:$i]:
% 15.46/15.67     ( ( l1_pre_topc @ A ) =>
% 15.46/15.67       ( ![B:$i]:
% 15.46/15.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.46/15.67           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 15.46/15.67  thf('9', plain,
% 15.46/15.67      (![X30 : $i, X31 : $i]:
% 15.46/15.67         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 15.46/15.67          | (r1_tarski @ (k1_tops_1 @ X31 @ X30) @ X30)
% 15.46/15.67          | ~ (l1_pre_topc @ X31))),
% 15.46/15.67      inference('cnf', [status(esa)], [t44_tops_1])).
% 15.46/15.67  thf('10', plain,
% 15.46/15.67      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 15.46/15.67      inference('sup-', [status(thm)], ['8', '9'])).
% 15.46/15.67  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 15.46/15.67      inference('demod', [status(thm)], ['10', '11'])).
% 15.46/15.67  thf('13', plain,
% 15.46/15.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf(fc9_tops_1, axiom,
% 15.46/15.67    (![A:$i,B:$i]:
% 15.46/15.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 15.46/15.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 15.46/15.67       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 15.46/15.67  thf('14', plain,
% 15.46/15.67      (![X26 : $i, X27 : $i]:
% 15.46/15.67         (~ (l1_pre_topc @ X26)
% 15.46/15.67          | ~ (v2_pre_topc @ X26)
% 15.46/15.67          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 15.46/15.67          | (v3_pre_topc @ (k1_tops_1 @ X26 @ X27) @ X26))),
% 15.46/15.67      inference('cnf', [status(esa)], [fc9_tops_1])).
% 15.46/15.67  thf('15', plain,
% 15.46/15.67      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 15.46/15.67        | ~ (v2_pre_topc @ sk_A)
% 15.46/15.67        | ~ (l1_pre_topc @ sk_A))),
% 15.46/15.67      inference('sup-', [status(thm)], ['13', '14'])).
% 15.46/15.67  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf('18', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 15.46/15.67      inference('demod', [status(thm)], ['15', '16', '17'])).
% 15.46/15.67  thf('19', plain,
% 15.46/15.67      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 15.46/15.67         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 15.46/15.67      inference('split', [status(esa)], ['0'])).
% 15.46/15.67  thf('20', plain,
% 15.46/15.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf(dt_k1_tops_1, axiom,
% 15.46/15.67    (![A:$i,B:$i]:
% 15.46/15.67     ( ( ( l1_pre_topc @ A ) & 
% 15.46/15.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 15.46/15.67       ( m1_subset_1 @
% 15.46/15.67         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 15.46/15.67  thf('21', plain,
% 15.46/15.67      (![X24 : $i, X25 : $i]:
% 15.46/15.67         (~ (l1_pre_topc @ X24)
% 15.46/15.67          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 15.46/15.67          | (m1_subset_1 @ (k1_tops_1 @ X24 @ X25) @ 
% 15.46/15.67             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 15.46/15.67      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 15.46/15.67  thf('22', plain,
% 15.46/15.67      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 15.46/15.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.46/15.67        | ~ (l1_pre_topc @ sk_A))),
% 15.46/15.67      inference('sup-', [status(thm)], ['20', '21'])).
% 15.46/15.67  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf('24', plain,
% 15.46/15.67      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 15.46/15.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.46/15.67      inference('demod', [status(thm)], ['22', '23'])).
% 15.46/15.67  thf('25', plain,
% 15.46/15.67      ((![X35 : $i]:
% 15.46/15.67          (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.46/15.67           | ~ (v3_pre_topc @ X35 @ sk_A)
% 15.46/15.67           | ~ (r1_tarski @ X35 @ sk_C)
% 15.46/15.67           | ~ (r2_hidden @ sk_B @ X35)))
% 15.46/15.67         <= ((![X35 : $i]:
% 15.46/15.67                (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.46/15.67                 | ~ (v3_pre_topc @ X35 @ sk_A)
% 15.46/15.67                 | ~ (r1_tarski @ X35 @ sk_C)
% 15.46/15.67                 | ~ (r2_hidden @ sk_B @ X35))))),
% 15.46/15.67      inference('split', [status(esa)], ['6'])).
% 15.46/15.67  thf('26', plain,
% 15.46/15.67      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 15.46/15.67         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 15.46/15.67         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 15.46/15.67         <= ((![X35 : $i]:
% 15.46/15.67                (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.46/15.67                 | ~ (v3_pre_topc @ X35 @ sk_A)
% 15.46/15.67                 | ~ (r1_tarski @ X35 @ sk_C)
% 15.46/15.67                 | ~ (r2_hidden @ sk_B @ X35))))),
% 15.46/15.67      inference('sup-', [status(thm)], ['24', '25'])).
% 15.46/15.67  thf('27', plain,
% 15.46/15.67      (((~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 15.46/15.67         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)))
% 15.46/15.67         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) & 
% 15.46/15.67             (![X35 : $i]:
% 15.46/15.67                (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.46/15.67                 | ~ (v3_pre_topc @ X35 @ sk_A)
% 15.46/15.67                 | ~ (r1_tarski @ X35 @ sk_C)
% 15.46/15.67                 | ~ (r2_hidden @ sk_B @ X35))))),
% 15.46/15.67      inference('sup-', [status(thm)], ['19', '26'])).
% 15.46/15.67  thf('28', plain,
% 15.46/15.67      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))
% 15.46/15.67         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) & 
% 15.46/15.67             (![X35 : $i]:
% 15.46/15.67                (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.46/15.67                 | ~ (v3_pre_topc @ X35 @ sk_A)
% 15.46/15.67                 | ~ (r1_tarski @ X35 @ sk_C)
% 15.46/15.67                 | ~ (r2_hidden @ sk_B @ X35))))),
% 15.46/15.67      inference('sup-', [status(thm)], ['18', '27'])).
% 15.46/15.67  thf('29', plain,
% 15.46/15.67      (~
% 15.46/15.67       (![X35 : $i]:
% 15.46/15.67          (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.46/15.67           | ~ (v3_pre_topc @ X35 @ sk_A)
% 15.46/15.67           | ~ (r1_tarski @ X35 @ sk_C)
% 15.46/15.67           | ~ (r2_hidden @ sk_B @ X35))) | 
% 15.46/15.67       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 15.46/15.67      inference('sup-', [status(thm)], ['12', '28'])).
% 15.46/15.67  thf('30', plain,
% 15.46/15.67      (((v3_pre_topc @ sk_D @ sk_A)
% 15.46/15.67        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf('31', plain,
% 15.46/15.67      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 15.46/15.67       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 15.46/15.67      inference('split', [status(esa)], ['30'])).
% 15.46/15.67  thf('32', plain,
% 15.46/15.67      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 15.46/15.67      inference('split', [status(esa)], ['30'])).
% 15.46/15.67  thf('33', plain,
% 15.46/15.67      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('split', [status(esa)], ['4'])).
% 15.46/15.67  thf(t30_tops_1, axiom,
% 15.46/15.67    (![A:$i]:
% 15.46/15.67     ( ( l1_pre_topc @ A ) =>
% 15.46/15.67       ( ![B:$i]:
% 15.46/15.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.46/15.67           ( ( v3_pre_topc @ B @ A ) <=>
% 15.46/15.67             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 15.46/15.67  thf('34', plain,
% 15.46/15.67      (![X28 : $i, X29 : $i]:
% 15.46/15.67         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 15.46/15.67          | ~ (v3_pre_topc @ X28 @ X29)
% 15.46/15.67          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 15.46/15.67          | ~ (l1_pre_topc @ X29))),
% 15.46/15.67      inference('cnf', [status(esa)], [t30_tops_1])).
% 15.46/15.67  thf('35', plain,
% 15.46/15.67      (((~ (l1_pre_topc @ sk_A)
% 15.46/15.67         | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 15.46/15.67         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup-', [status(thm)], ['33', '34'])).
% 15.46/15.67  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf('37', plain,
% 15.46/15.67      ((((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 15.46/15.67         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('demod', [status(thm)], ['35', '36'])).
% 15.46/15.67  thf('38', plain,
% 15.46/15.67      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A))
% 15.46/15.67         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 15.46/15.67             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup-', [status(thm)], ['32', '37'])).
% 15.46/15.67  thf('39', plain,
% 15.46/15.67      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('split', [status(esa)], ['4'])).
% 15.46/15.67  thf(dt_k3_subset_1, axiom,
% 15.46/15.67    (![A:$i,B:$i]:
% 15.46/15.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 15.46/15.67       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 15.46/15.67  thf('40', plain,
% 15.46/15.67      (![X16 : $i, X17 : $i]:
% 15.46/15.67         ((m1_subset_1 @ (k3_subset_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 15.46/15.67          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 15.46/15.67      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 15.46/15.67  thf('41', plain,
% 15.46/15.67      (((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 15.46/15.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup-', [status(thm)], ['39', '40'])).
% 15.46/15.67  thf(t52_pre_topc, axiom,
% 15.46/15.67    (![A:$i]:
% 15.46/15.67     ( ( l1_pre_topc @ A ) =>
% 15.46/15.67       ( ![B:$i]:
% 15.46/15.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.46/15.67           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 15.46/15.67             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 15.46/15.67               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 15.46/15.67  thf('42', plain,
% 15.46/15.67      (![X20 : $i, X21 : $i]:
% 15.46/15.67         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 15.46/15.67          | ~ (v4_pre_topc @ X20 @ X21)
% 15.46/15.67          | ((k2_pre_topc @ X21 @ X20) = (X20))
% 15.46/15.67          | ~ (l1_pre_topc @ X21))),
% 15.46/15.67      inference('cnf', [status(esa)], [t52_pre_topc])).
% 15.46/15.67  thf('43', plain,
% 15.46/15.67      (((~ (l1_pre_topc @ sk_A)
% 15.46/15.67         | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 15.46/15.67             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 15.46/15.67         | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup-', [status(thm)], ['41', '42'])).
% 15.46/15.67  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf('45', plain,
% 15.46/15.67      (((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 15.46/15.67           = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 15.46/15.67         | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('demod', [status(thm)], ['43', '44'])).
% 15.46/15.67  thf('46', plain,
% 15.46/15.67      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 15.46/15.67          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 15.46/15.67         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 15.46/15.67             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup-', [status(thm)], ['38', '45'])).
% 15.46/15.67  thf('47', plain,
% 15.46/15.67      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('split', [status(esa)], ['4'])).
% 15.46/15.67  thf(d1_tops_1, axiom,
% 15.46/15.67    (![A:$i]:
% 15.46/15.67     ( ( l1_pre_topc @ A ) =>
% 15.46/15.67       ( ![B:$i]:
% 15.46/15.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.46/15.67           ( ( k1_tops_1 @ A @ B ) =
% 15.46/15.67             ( k3_subset_1 @
% 15.46/15.67               ( u1_struct_0 @ A ) @ 
% 15.46/15.67               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 15.46/15.67  thf('48', plain,
% 15.46/15.67      (![X22 : $i, X23 : $i]:
% 15.46/15.67         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 15.46/15.67          | ((k1_tops_1 @ X23 @ X22)
% 15.46/15.67              = (k3_subset_1 @ (u1_struct_0 @ X23) @ 
% 15.46/15.67                 (k2_pre_topc @ X23 @ (k3_subset_1 @ (u1_struct_0 @ X23) @ X22))))
% 15.46/15.67          | ~ (l1_pre_topc @ X23))),
% 15.46/15.67      inference('cnf', [status(esa)], [d1_tops_1])).
% 15.46/15.67  thf('49', plain,
% 15.46/15.67      (((~ (l1_pre_topc @ sk_A)
% 15.46/15.67         | ((k1_tops_1 @ sk_A @ sk_D)
% 15.46/15.67             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.46/15.67                (k2_pre_topc @ sk_A @ 
% 15.46/15.67                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup-', [status(thm)], ['47', '48'])).
% 15.46/15.67  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf('51', plain,
% 15.46/15.67      ((((k1_tops_1 @ sk_A @ sk_D)
% 15.46/15.67          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.46/15.67             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('demod', [status(thm)], ['49', '50'])).
% 15.46/15.67  thf('52', plain,
% 15.46/15.67      ((((k1_tops_1 @ sk_A @ sk_D)
% 15.46/15.67          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.46/15.67             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))
% 15.46/15.67         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 15.46/15.67             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup+', [status(thm)], ['46', '51'])).
% 15.46/15.67  thf('53', plain,
% 15.46/15.67      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('split', [status(esa)], ['4'])).
% 15.46/15.67  thf(involutiveness_k3_subset_1, axiom,
% 15.46/15.67    (![A:$i,B:$i]:
% 15.46/15.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 15.46/15.67       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 15.46/15.67  thf('54', plain,
% 15.46/15.67      (![X18 : $i, X19 : $i]:
% 15.46/15.67         (((k3_subset_1 @ X19 @ (k3_subset_1 @ X19 @ X18)) = (X18))
% 15.46/15.67          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 15.46/15.67      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 15.46/15.67  thf('55', plain,
% 15.46/15.67      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.46/15.67          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup-', [status(thm)], ['53', '54'])).
% 15.46/15.67  thf('56', plain,
% 15.46/15.67      ((((k1_tops_1 @ sk_A @ sk_D) = (sk_D)))
% 15.46/15.67         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 15.46/15.67             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup+', [status(thm)], ['52', '55'])).
% 15.46/15.67  thf('57', plain,
% 15.46/15.67      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 15.46/15.67      inference('split', [status(esa)], ['2'])).
% 15.46/15.67  thf('58', plain,
% 15.46/15.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf('59', plain,
% 15.46/15.67      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('split', [status(esa)], ['4'])).
% 15.46/15.67  thf(t48_tops_1, axiom,
% 15.46/15.67    (![A:$i]:
% 15.46/15.67     ( ( l1_pre_topc @ A ) =>
% 15.46/15.67       ( ![B:$i]:
% 15.46/15.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.46/15.67           ( ![C:$i]:
% 15.46/15.67             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.46/15.67               ( ( r1_tarski @ B @ C ) =>
% 15.46/15.67                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 15.46/15.67  thf('60', plain,
% 15.46/15.67      (![X32 : $i, X33 : $i, X34 : $i]:
% 15.46/15.67         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 15.46/15.67          | ~ (r1_tarski @ X32 @ X34)
% 15.46/15.67          | (r1_tarski @ (k1_tops_1 @ X33 @ X32) @ (k1_tops_1 @ X33 @ X34))
% 15.46/15.67          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 15.46/15.67          | ~ (l1_pre_topc @ X33))),
% 15.46/15.67      inference('cnf', [status(esa)], [t48_tops_1])).
% 15.46/15.67  thf('61', plain,
% 15.46/15.67      ((![X0 : $i]:
% 15.46/15.67          (~ (l1_pre_topc @ sk_A)
% 15.46/15.67           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.46/15.67           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 15.46/15.67           | ~ (r1_tarski @ sk_D @ X0)))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup-', [status(thm)], ['59', '60'])).
% 15.46/15.67  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 15.46/15.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.46/15.67  thf('63', plain,
% 15.46/15.67      ((![X0 : $i]:
% 15.46/15.67          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.46/15.67           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 15.46/15.67           | ~ (r1_tarski @ sk_D @ X0)))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('demod', [status(thm)], ['61', '62'])).
% 15.46/15.67  thf('64', plain,
% 15.46/15.67      (((~ (r1_tarski @ sk_D @ sk_C)
% 15.46/15.67         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C))))
% 15.46/15.67         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup-', [status(thm)], ['58', '63'])).
% 15.46/15.67  thf('65', plain,
% 15.46/15.67      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C)))
% 15.46/15.67         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 15.46/15.67             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup-', [status(thm)], ['57', '64'])).
% 15.46/15.67  thf(t12_xboole_1, axiom,
% 15.46/15.67    (![A:$i,B:$i]:
% 15.46/15.67     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 15.46/15.67  thf('66', plain,
% 15.46/15.67      (![X6 : $i, X7 : $i]:
% 15.46/15.67         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 15.46/15.67      inference('cnf', [status(esa)], [t12_xboole_1])).
% 15.46/15.67  thf('67', plain,
% 15.46/15.67      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C))
% 15.46/15.67          = (k1_tops_1 @ sk_A @ sk_C)))
% 15.46/15.67         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 15.46/15.67             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup-', [status(thm)], ['65', '66'])).
% 15.46/15.67  thf('68', plain,
% 15.46/15.67      ((((k2_xboole_0 @ sk_D @ (k1_tops_1 @ sk_A @ sk_C))
% 15.46/15.67          = (k1_tops_1 @ sk_A @ sk_C)))
% 15.46/15.67         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 15.46/15.67             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 15.46/15.67             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup+', [status(thm)], ['56', '67'])).
% 15.46/15.67  thf(t7_xboole_1, axiom,
% 15.46/15.67    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 15.46/15.67  thf('69', plain,
% 15.46/15.67      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 15.46/15.67      inference('cnf', [status(esa)], [t7_xboole_1])).
% 15.46/15.67  thf(d10_xboole_0, axiom,
% 15.46/15.67    (![A:$i,B:$i]:
% 15.46/15.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 15.46/15.67  thf('70', plain,
% 15.46/15.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 15.46/15.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.46/15.67  thf('71', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 15.46/15.67      inference('simplify', [status(thm)], ['70'])).
% 15.46/15.67  thf(t10_xboole_1, axiom,
% 15.46/15.67    (![A:$i,B:$i,C:$i]:
% 15.46/15.67     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 15.46/15.67  thf('72', plain,
% 15.46/15.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 15.46/15.67         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 15.46/15.67      inference('cnf', [status(esa)], [t10_xboole_1])).
% 15.46/15.67  thf('73', plain,
% 15.46/15.67      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 15.46/15.67      inference('sup-', [status(thm)], ['71', '72'])).
% 15.46/15.67  thf(t8_xboole_1, axiom,
% 15.46/15.67    (![A:$i,B:$i,C:$i]:
% 15.46/15.67     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 15.46/15.67       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 15.46/15.67  thf('74', plain,
% 15.46/15.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.46/15.67         (~ (r1_tarski @ X10 @ X11)
% 15.46/15.67          | ~ (r1_tarski @ X12 @ X11)
% 15.46/15.67          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 15.46/15.67      inference('cnf', [status(esa)], [t8_xboole_1])).
% 15.46/15.67  thf('75', plain,
% 15.46/15.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.46/15.67         ((r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 15.46/15.67          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.46/15.67      inference('sup-', [status(thm)], ['73', '74'])).
% 15.46/15.67  thf('76', plain,
% 15.46/15.67      (![X0 : $i, X1 : $i]:
% 15.46/15.67         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 15.46/15.67      inference('sup-', [status(thm)], ['69', '75'])).
% 15.46/15.67  thf('77', plain,
% 15.46/15.67      (![X0 : $i, X2 : $i]:
% 15.46/15.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 15.46/15.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.46/15.67  thf('78', plain,
% 15.46/15.67      (![X0 : $i, X1 : $i]:
% 15.46/15.67         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 15.46/15.67          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 15.46/15.67      inference('sup-', [status(thm)], ['76', '77'])).
% 15.46/15.67  thf('79', plain,
% 15.46/15.67      (![X0 : $i, X1 : $i]:
% 15.46/15.67         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 15.46/15.67      inference('sup-', [status(thm)], ['69', '75'])).
% 15.46/15.67  thf('80', plain,
% 15.46/15.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.46/15.67      inference('demod', [status(thm)], ['78', '79'])).
% 15.46/15.67  thf('81', plain,
% 15.46/15.67      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 15.46/15.67      inference('split', [status(esa)], ['0'])).
% 15.46/15.67  thf(l1_zfmisc_1, axiom,
% 15.46/15.67    (![A:$i,B:$i]:
% 15.46/15.67     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 15.46/15.67  thf('82', plain,
% 15.46/15.67      (![X13 : $i, X15 : $i]:
% 15.46/15.67         ((r1_tarski @ (k1_tarski @ X13) @ X15) | ~ (r2_hidden @ X13 @ X15))),
% 15.46/15.67      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 15.46/15.67  thf('83', plain,
% 15.46/15.67      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_D))
% 15.46/15.67         <= (((r2_hidden @ sk_B @ sk_D)))),
% 15.46/15.67      inference('sup-', [status(thm)], ['81', '82'])).
% 15.46/15.67  thf('84', plain,
% 15.46/15.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 15.46/15.67         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 15.46/15.67      inference('cnf', [status(esa)], [t10_xboole_1])).
% 15.46/15.67  thf('85', plain,
% 15.46/15.67      ((![X0 : $i]:
% 15.46/15.67          (r1_tarski @ (k1_tarski @ sk_B) @ (k2_xboole_0 @ X0 @ sk_D)))
% 15.46/15.67         <= (((r2_hidden @ sk_B @ sk_D)))),
% 15.46/15.67      inference('sup-', [status(thm)], ['83', '84'])).
% 15.46/15.67  thf('86', plain,
% 15.46/15.67      (![X13 : $i, X14 : $i]:
% 15.46/15.67         ((r2_hidden @ X13 @ X14) | ~ (r1_tarski @ (k1_tarski @ X13) @ X14))),
% 15.46/15.67      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 15.46/15.67  thf('87', plain,
% 15.46/15.67      ((![X0 : $i]: (r2_hidden @ sk_B @ (k2_xboole_0 @ X0 @ sk_D)))
% 15.46/15.67         <= (((r2_hidden @ sk_B @ sk_D)))),
% 15.46/15.67      inference('sup-', [status(thm)], ['85', '86'])).
% 15.46/15.67  thf('88', plain,
% 15.46/15.67      ((![X0 : $i]: (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_D @ X0)))
% 15.46/15.67         <= (((r2_hidden @ sk_B @ sk_D)))),
% 15.46/15.67      inference('sup+', [status(thm)], ['80', '87'])).
% 15.46/15.67  thf('89', plain,
% 15.46/15.67      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 15.46/15.67         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 15.46/15.67             ((r1_tarski @ sk_D @ sk_C)) & 
% 15.46/15.67             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 15.46/15.67             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.46/15.67      inference('sup+', [status(thm)], ['68', '88'])).
% 15.46/15.67  thf('90', plain,
% 15.46/15.67      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 15.46/15.67         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 15.46/15.67      inference('split', [status(esa)], ['6'])).
% 15.46/15.67  thf('91', plain,
% 15.46/15.67      (~ ((v3_pre_topc @ sk_D @ sk_A)) | 
% 15.46/15.67       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 15.46/15.67       ~ ((r1_tarski @ sk_D @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_D)) | 
% 15.46/15.67       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 15.46/15.67      inference('sup-', [status(thm)], ['89', '90'])).
% 15.46/15.67  thf('92', plain, ($false),
% 15.46/15.67      inference('sat_resolution*', [status(thm)],
% 15.46/15.67                ['1', '3', '5', '7', '29', '31', '91'])).
% 15.46/15.67  
% 15.46/15.67  % SZS output end Refutation
% 15.46/15.67  
% 15.46/15.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
