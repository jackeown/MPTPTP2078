%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nNWGiBSd18

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 178 expanded)
%              Number of leaves         :   31 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          : 1162 (2801 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X27 @ sk_A )
      | ~ ( r1_tarski @ X27 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X27 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X27 ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('10',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X27 ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X27 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('21',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X27 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X23 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X27 ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
   <= ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      & ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X27 @ sk_A )
          | ~ ( r1_tarski @ X27 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X27 ) ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,
    ( ~ ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X27 @ sk_A )
          | ~ ( r1_tarski @ X27 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X27 ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','28'])).

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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_pre_topc @ X12 @ X13 )
      | ( ( k2_pre_topc @ X13 @ X12 )
        = X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k1_tops_1 @ X15 @ X14 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k2_pre_topc @ X15 @ ( k3_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 ) ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r1_tarski @ X24 @ X26 )
      | ( r1_tarski @ ( k1_tops_1 @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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

thf('66',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['56','65'])).

thf('67',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('68',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X5 ) @ X7 )
      | ~ ( r2_hidden @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('69',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('71',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_D )
      = sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D @ X0 )
        | ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k1_tarski @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('76',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('78',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_D @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','29','31','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nNWGiBSd18
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:08:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.59  % Solved by: fo/fo7.sh
% 0.22/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.59  % done 271 iterations in 0.124s
% 0.22/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.59  % SZS output start Refutation
% 0.22/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.59  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.59  thf(t54_tops_1, conjecture,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.59       ( ![B:$i,C:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.22/0.59             ( ?[D:$i]:
% 0.22/0.59               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.22/0.59                 ( v3_pre_topc @ D @ A ) & 
% 0.22/0.59                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.22/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.59    (~( ![A:$i]:
% 0.22/0.59        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.59          ( ![B:$i,C:$i]:
% 0.22/0.59            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.22/0.59                ( ?[D:$i]:
% 0.22/0.59                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.22/0.59                    ( v3_pre_topc @ D @ A ) & 
% 0.22/0.59                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.22/0.59    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 0.22/0.59  thf('0', plain,
% 0.22/0.59      (((r2_hidden @ sk_B @ sk_D)
% 0.22/0.59        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('1', plain,
% 0.22/0.59      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.22/0.59       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.22/0.59      inference('split', [status(esa)], ['0'])).
% 0.22/0.59  thf('2', plain,
% 0.22/0.59      (((r1_tarski @ sk_D @ sk_C)
% 0.22/0.59        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('3', plain,
% 0.22/0.59      (((r1_tarski @ sk_D @ sk_C)) | 
% 0.22/0.59       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.22/0.59      inference('split', [status(esa)], ['2'])).
% 0.22/0.59  thf('4', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('5', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.22/0.59       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.22/0.59      inference('split', [status(esa)], ['4'])).
% 0.22/0.59  thf('6', plain,
% 0.22/0.59      (![X27 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59          | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.22/0.59          | ~ (r1_tarski @ X27 @ sk_C)
% 0.22/0.59          | ~ (r2_hidden @ sk_B @ X27)
% 0.22/0.59          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('7', plain,
% 0.22/0.59      ((![X27 : $i]:
% 0.22/0.59          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.22/0.59           | ~ (r1_tarski @ X27 @ sk_C)
% 0.22/0.59           | ~ (r2_hidden @ sk_B @ X27))) | 
% 0.22/0.59       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.22/0.59      inference('split', [status(esa)], ['6'])).
% 0.22/0.59  thf('8', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(fc9_tops_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.22/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.59       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.22/0.59  thf('9', plain,
% 0.22/0.59      (![X18 : $i, X19 : $i]:
% 0.22/0.59         (~ (l1_pre_topc @ X18)
% 0.22/0.59          | ~ (v2_pre_topc @ X18)
% 0.22/0.59          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.59          | (v3_pre_topc @ (k1_tops_1 @ X18 @ X19) @ X18))),
% 0.22/0.59      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.22/0.59  thf('10', plain,
% 0.22/0.59      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.22/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.59  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('13', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.22/0.59      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.22/0.59  thf('14', plain,
% 0.22/0.59      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.22/0.59         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.22/0.59      inference('split', [status(esa)], ['0'])).
% 0.22/0.59  thf('15', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(dt_k1_tops_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( ( l1_pre_topc @ A ) & 
% 0.22/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.59       ( m1_subset_1 @
% 0.22/0.59         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.59  thf('16', plain,
% 0.22/0.59      (![X16 : $i, X17 : $i]:
% 0.22/0.59         (~ (l1_pre_topc @ X16)
% 0.22/0.59          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.59          | (m1_subset_1 @ (k1_tops_1 @ X16 @ X17) @ 
% 0.22/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.22/0.59      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.22/0.59  thf('17', plain,
% 0.22/0.59      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.22/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.59  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('19', plain,
% 0.22/0.59      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.22/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.59  thf('20', plain,
% 0.22/0.59      ((![X27 : $i]:
% 0.22/0.59          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.22/0.59           | ~ (r1_tarski @ X27 @ sk_C)
% 0.22/0.59           | ~ (r2_hidden @ sk_B @ X27)))
% 0.22/0.59         <= ((![X27 : $i]:
% 0.22/0.59                (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.22/0.59                 | ~ (r1_tarski @ X27 @ sk_C)
% 0.22/0.59                 | ~ (r2_hidden @ sk_B @ X27))))),
% 0.22/0.59      inference('split', [status(esa)], ['6'])).
% 0.22/0.59  thf('21', plain,
% 0.22/0.59      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.22/0.59         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.22/0.59         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.22/0.59         <= ((![X27 : $i]:
% 0.22/0.59                (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.22/0.59                 | ~ (r1_tarski @ X27 @ sk_C)
% 0.22/0.59                 | ~ (r2_hidden @ sk_B @ X27))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.59  thf('22', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(t44_tops_1, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( l1_pre_topc @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.22/0.59  thf('23', plain,
% 0.22/0.59      (![X22 : $i, X23 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.22/0.59          | (r1_tarski @ (k1_tops_1 @ X23 @ X22) @ X22)
% 0.22/0.59          | ~ (l1_pre_topc @ X23))),
% 0.22/0.59      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.22/0.59  thf('24', plain,
% 0.22/0.59      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.22/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.59  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('26', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.22/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.59  thf('27', plain,
% 0.22/0.59      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.22/0.59         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.22/0.59         <= ((![X27 : $i]:
% 0.22/0.59                (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.22/0.59                 | ~ (r1_tarski @ X27 @ sk_C)
% 0.22/0.59                 | ~ (r2_hidden @ sk_B @ X27))))),
% 0.22/0.59      inference('demod', [status(thm)], ['21', '26'])).
% 0.22/0.59  thf('28', plain,
% 0.22/0.59      ((~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A))
% 0.22/0.59         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) & 
% 0.22/0.59             (![X27 : $i]:
% 0.22/0.59                (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.22/0.59                 | ~ (r1_tarski @ X27 @ sk_C)
% 0.22/0.59                 | ~ (r2_hidden @ sk_B @ X27))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['14', '27'])).
% 0.22/0.59  thf('29', plain,
% 0.22/0.59      (~
% 0.22/0.59       (![X27 : $i]:
% 0.22/0.59          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.22/0.59           | ~ (r1_tarski @ X27 @ sk_C)
% 0.22/0.59           | ~ (r2_hidden @ sk_B @ X27))) | 
% 0.22/0.59       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['13', '28'])).
% 0.22/0.59  thf('30', plain,
% 0.22/0.59      (((v3_pre_topc @ sk_D @ sk_A)
% 0.22/0.59        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('31', plain,
% 0.22/0.59      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.22/0.59       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.22/0.59      inference('split', [status(esa)], ['30'])).
% 0.22/0.59  thf('32', plain,
% 0.22/0.59      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.22/0.59      inference('split', [status(esa)], ['30'])).
% 0.22/0.59  thf('33', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('split', [status(esa)], ['4'])).
% 0.22/0.59  thf(t30_tops_1, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( l1_pre_topc @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( ( v3_pre_topc @ B @ A ) <=>
% 0.22/0.59             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.22/0.59  thf('34', plain,
% 0.22/0.59      (![X20 : $i, X21 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.22/0.59          | ~ (v3_pre_topc @ X20 @ X21)
% 0.22/0.59          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.22/0.59          | ~ (l1_pre_topc @ X21))),
% 0.22/0.59      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.22/0.59  thf('35', plain,
% 0.22/0.59      (((~ (l1_pre_topc @ sk_A)
% 0.22/0.59         | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.22/0.59         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.59  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('37', plain,
% 0.22/0.59      ((((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.22/0.59         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.59  thf('38', plain,
% 0.22/0.59      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A))
% 0.22/0.59         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.22/0.59             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['32', '37'])).
% 0.22/0.59  thf('39', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('split', [status(esa)], ['4'])).
% 0.22/0.59  thf(dt_k3_subset_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.59       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.59  thf('40', plain,
% 0.22/0.59      (![X8 : $i, X9 : $i]:
% 0.22/0.59         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.22/0.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.59      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.59  thf('41', plain,
% 0.22/0.59      (((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.22/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.59  thf(t52_pre_topc, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( l1_pre_topc @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.22/0.59             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.22/0.59               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.22/0.59  thf('42', plain,
% 0.22/0.59      (![X12 : $i, X13 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.59          | ~ (v4_pre_topc @ X12 @ X13)
% 0.22/0.59          | ((k2_pre_topc @ X13 @ X12) = (X12))
% 0.22/0.59          | ~ (l1_pre_topc @ X13))),
% 0.22/0.59      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.22/0.59  thf('43', plain,
% 0.22/0.59      (((~ (l1_pre_topc @ sk_A)
% 0.22/0.59         | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.22/0.59             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.22/0.59         | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.59  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('45', plain,
% 0.22/0.59      (((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.22/0.59           = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.22/0.59         | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.59  thf('46', plain,
% 0.22/0.59      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.22/0.59          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.22/0.59         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.22/0.59             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['38', '45'])).
% 0.22/0.59  thf('47', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('split', [status(esa)], ['4'])).
% 0.22/0.59  thf(d1_tops_1, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( l1_pre_topc @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( ( k1_tops_1 @ A @ B ) =
% 0.22/0.59             ( k3_subset_1 @
% 0.22/0.59               ( u1_struct_0 @ A ) @ 
% 0.22/0.59               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.22/0.59  thf('48', plain,
% 0.22/0.59      (![X14 : $i, X15 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.59          | ((k1_tops_1 @ X15 @ X14)
% 0.22/0.59              = (k3_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.22/0.59                 (k2_pre_topc @ X15 @ (k3_subset_1 @ (u1_struct_0 @ X15) @ X14))))
% 0.22/0.59          | ~ (l1_pre_topc @ X15))),
% 0.22/0.59      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.22/0.59  thf('49', plain,
% 0.22/0.59      (((~ (l1_pre_topc @ sk_A)
% 0.22/0.59         | ((k1_tops_1 @ sk_A @ sk_D)
% 0.22/0.59             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.59                (k2_pre_topc @ sk_A @ 
% 0.22/0.59                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.59  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('51', plain,
% 0.22/0.59      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.22/0.59          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.59             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('demod', [status(thm)], ['49', '50'])).
% 0.22/0.59  thf('52', plain,
% 0.22/0.59      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.22/0.59          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.59             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))
% 0.22/0.59         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.22/0.59             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup+', [status(thm)], ['46', '51'])).
% 0.22/0.59  thf('53', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('split', [status(esa)], ['4'])).
% 0.22/0.59  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.59       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.59  thf('54', plain,
% 0.22/0.59      (![X10 : $i, X11 : $i]:
% 0.22/0.59         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.22/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.59      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.59  thf('55', plain,
% 0.22/0.59      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.59          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.59  thf('56', plain,
% 0.22/0.59      ((((k1_tops_1 @ sk_A @ sk_D) = (sk_D)))
% 0.22/0.59         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.22/0.59             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup+', [status(thm)], ['52', '55'])).
% 0.22/0.59  thf('57', plain,
% 0.22/0.59      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.22/0.59      inference('split', [status(esa)], ['2'])).
% 0.22/0.59  thf('58', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('59', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('split', [status(esa)], ['4'])).
% 0.22/0.59  thf(t48_tops_1, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( l1_pre_topc @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( ![C:$i]:
% 0.22/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59               ( ( r1_tarski @ B @ C ) =>
% 0.22/0.59                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.22/0.59  thf('60', plain,
% 0.22/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.22/0.59          | ~ (r1_tarski @ X24 @ X26)
% 0.22/0.59          | (r1_tarski @ (k1_tops_1 @ X25 @ X24) @ (k1_tops_1 @ X25 @ X26))
% 0.22/0.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.22/0.59          | ~ (l1_pre_topc @ X25))),
% 0.22/0.59      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.22/0.59  thf('61', plain,
% 0.22/0.59      ((![X0 : $i]:
% 0.22/0.59          (~ (l1_pre_topc @ sk_A)
% 0.22/0.59           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.22/0.59           | ~ (r1_tarski @ sk_D @ X0)))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.59  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('63', plain,
% 0.22/0.59      ((![X0 : $i]:
% 0.22/0.59          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.22/0.59           | ~ (r1_tarski @ sk_D @ X0)))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.59  thf('64', plain,
% 0.22/0.59      (((~ (r1_tarski @ sk_D @ sk_C)
% 0.22/0.59         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.22/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['58', '63'])).
% 0.22/0.59  thf('65', plain,
% 0.22/0.59      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.22/0.59         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.22/0.59             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['57', '64'])).
% 0.22/0.59  thf('66', plain,
% 0.22/0.59      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.22/0.59         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.22/0.59             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.22/0.59             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup+', [status(thm)], ['56', '65'])).
% 0.22/0.59  thf('67', plain,
% 0.22/0.59      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.22/0.59      inference('split', [status(esa)], ['0'])).
% 0.22/0.59  thf(l1_zfmisc_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.59  thf('68', plain,
% 0.22/0.59      (![X5 : $i, X7 : $i]:
% 0.22/0.59         ((r1_tarski @ (k1_tarski @ X5) @ X7) | ~ (r2_hidden @ X5 @ X7))),
% 0.22/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.59  thf('69', plain,
% 0.22/0.59      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_D))
% 0.22/0.59         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.59  thf(t12_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.59  thf('70', plain,
% 0.22/0.59      (![X3 : $i, X4 : $i]:
% 0.22/0.59         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.22/0.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.59  thf('71', plain,
% 0.22/0.59      ((((k2_xboole_0 @ (k1_tarski @ sk_B) @ sk_D) = (sk_D)))
% 0.22/0.59         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['69', '70'])).
% 0.22/0.59  thf(t11_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i,C:$i]:
% 0.22/0.59     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.22/0.59  thf('72', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.59         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.22/0.59      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.22/0.59  thf('73', plain,
% 0.22/0.59      ((![X0 : $i]:
% 0.22/0.59          (~ (r1_tarski @ sk_D @ X0) | (r1_tarski @ (k1_tarski @ sk_B) @ X0)))
% 0.22/0.59         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['71', '72'])).
% 0.22/0.59  thf('74', plain,
% 0.22/0.59      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.22/0.59         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.22/0.59             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.22/0.59             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.22/0.59             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['66', '73'])).
% 0.22/0.59  thf('75', plain,
% 0.22/0.59      (![X5 : $i, X6 : $i]:
% 0.22/0.59         ((r2_hidden @ X5 @ X6) | ~ (r1_tarski @ (k1_tarski @ X5) @ X6))),
% 0.22/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.59  thf('76', plain,
% 0.22/0.59      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.22/0.59         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.22/0.59             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.22/0.59             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.22/0.59             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['74', '75'])).
% 0.22/0.59  thf('77', plain,
% 0.22/0.59      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.22/0.59         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.22/0.59      inference('split', [status(esa)], ['6'])).
% 0.22/0.59  thf('78', plain,
% 0.22/0.59      (~ ((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.22/0.59       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.22/0.59       ~ ((r1_tarski @ sk_D @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_D)) | 
% 0.22/0.59       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['76', '77'])).
% 0.22/0.59  thf('79', plain, ($false),
% 0.22/0.59      inference('sat_resolution*', [status(thm)],
% 0.22/0.59                ['1', '3', '5', '7', '29', '31', '78'])).
% 0.22/0.59  
% 0.22/0.59  % SZS output end Refutation
% 0.22/0.59  
% 0.22/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
