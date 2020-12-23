%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N0DelBfuQ5

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:06 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 601 expanded)
%              Number of leaves         :   27 ( 165 expanded)
%              Depth                    :   22
%              Number of atoms          : 1092 (10388 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X26 @ sk_A )
      | ~ ( r1_tarski @ X26 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_B @ X26 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X22 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X26 ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X17 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('19',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference(demod,[status(thm)],['16','22'])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      & ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X26 @ sk_A )
          | ~ ( r1_tarski @ X26 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X26 ) ) ) ),
    inference('sup-',[status(thm)],['9','23'])).

thf('25',plain,
    ( ~ ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X26 @ sk_A )
          | ~ ( r1_tarski @ X26 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X26 ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('29',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('30',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['2','25','29'])).

thf('31',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['33'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['34','36'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( r1_tarski @ X23 @ X25 )
      | ( r1_tarski @ ( k1_tops_1 @ X24 @ X23 ) @ ( k1_tops_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k1_tops_1 @ X14 @ X13 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k2_pre_topc @ X14 @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('44',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_D )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','35'])).

thf('51',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['49','50'])).

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

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_pre_topc @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('56',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ( v4_pre_topc @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('57',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('61',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['57','58','61'])).

thf('63',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['63'])).

thf('66',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','25','65'])).

thf('67',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['64','66'])).

thf('68',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','35'])).

thf('70',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['53','54','70'])).

thf('72',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','35'])).

thf('74',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','35'])).

thf('77',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = sk_D ),
    inference(simpl_trail,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = sk_D ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['41','78'])).

thf('80',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C_1 )
    | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','79'])).

thf('81',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['81'])).

thf('84',plain,(
    r1_tarski @ sk_D @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','25','83'])).

thf('85',plain,(
    r1_tarski @ sk_D @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['82','84'])).

thf('86',plain,(
    r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['80','85'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['27','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N0DelBfuQ5
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:46:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.90/1.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.13  % Solved by: fo/fo7.sh
% 0.90/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.13  % done 839 iterations in 0.694s
% 0.90/1.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.13  % SZS output start Refutation
% 0.90/1.13  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.90/1.13  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.90/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.13  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.13  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.90/1.13  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.90/1.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.13  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.90/1.13  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.90/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.13  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.13  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.90/1.13  thf(t54_tops_1, conjecture,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.13       ( ![B:$i,C:$i]:
% 0.90/1.13         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.13           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.90/1.13             ( ?[D:$i]:
% 0.90/1.13               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.90/1.13                 ( v3_pre_topc @ D @ A ) & 
% 0.90/1.13                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.90/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.13    (~( ![A:$i]:
% 0.90/1.13        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.13          ( ![B:$i,C:$i]:
% 0.90/1.13            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.13              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.90/1.13                ( ?[D:$i]:
% 0.90/1.13                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.90/1.13                    ( v3_pre_topc @ D @ A ) & 
% 0.90/1.13                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.90/1.13    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 0.90/1.13  thf('0', plain,
% 0.90/1.13      (![X26 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.13          | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.90/1.13          | ~ (r1_tarski @ X26 @ sk_C_1)
% 0.90/1.13          | ~ (r2_hidden @ sk_B @ X26)
% 0.90/1.13          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('1', plain,
% 0.90/1.13      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.90/1.13         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 0.90/1.13      inference('split', [status(esa)], ['0'])).
% 0.90/1.13  thf('2', plain,
% 0.90/1.13      (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))) | 
% 0.90/1.13       (![X26 : $i]:
% 0.90/1.13          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.13           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.90/1.13           | ~ (r1_tarski @ X26 @ sk_C_1)
% 0.90/1.13           | ~ (r2_hidden @ sk_B @ X26)))),
% 0.90/1.13      inference('split', [status(esa)], ['0'])).
% 0.90/1.13  thf('3', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(t44_tops_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.13           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.90/1.13  thf('4', plain,
% 0.90/1.13      (![X21 : $i, X22 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.90/1.13          | (r1_tarski @ (k1_tops_1 @ X22 @ X21) @ X21)
% 0.90/1.13          | ~ (l1_pre_topc @ X22))),
% 0.90/1.13      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.90/1.13  thf('5', plain,
% 0.90/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.13        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.90/1.13      inference('sup-', [status(thm)], ['3', '4'])).
% 0.90/1.13  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('7', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.90/1.13      inference('demod', [status(thm)], ['5', '6'])).
% 0.90/1.13  thf('8', plain,
% 0.90/1.13      (((r2_hidden @ sk_B @ sk_D)
% 0.90/1.13        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('9', plain,
% 0.90/1.13      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.90/1.13         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 0.90/1.13      inference('split', [status(esa)], ['8'])).
% 0.90/1.13  thf('10', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(dt_k1_tops_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( l1_pre_topc @ A ) & 
% 0.90/1.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.13       ( m1_subset_1 @
% 0.90/1.13         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.90/1.13  thf('11', plain,
% 0.90/1.13      (![X15 : $i, X16 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X15)
% 0.90/1.13          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.90/1.13          | (m1_subset_1 @ (k1_tops_1 @ X15 @ X16) @ 
% 0.90/1.13             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.90/1.13  thf('12', plain,
% 0.90/1.13      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.90/1.13         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.13        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.13      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.13  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('14', plain,
% 0.90/1.13      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.90/1.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.13      inference('demod', [status(thm)], ['12', '13'])).
% 0.90/1.13  thf('15', plain,
% 0.90/1.13      ((![X26 : $i]:
% 0.90/1.13          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.13           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.90/1.13           | ~ (r1_tarski @ X26 @ sk_C_1)
% 0.90/1.13           | ~ (r2_hidden @ sk_B @ X26)))
% 0.90/1.13         <= ((![X26 : $i]:
% 0.90/1.13                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.13                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.90/1.13                 | ~ (r1_tarski @ X26 @ sk_C_1)
% 0.90/1.13                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.90/1.13      inference('split', [status(esa)], ['0'])).
% 0.90/1.13  thf('16', plain,
% 0.90/1.13      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.90/1.13         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 0.90/1.13         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 0.90/1.13         <= ((![X26 : $i]:
% 0.90/1.13                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.13                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.90/1.13                 | ~ (r1_tarski @ X26 @ sk_C_1)
% 0.90/1.13                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['14', '15'])).
% 0.90/1.13  thf('17', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(fc9_tops_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.90/1.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.13       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.90/1.13  thf('18', plain,
% 0.90/1.13      (![X17 : $i, X18 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X17)
% 0.90/1.13          | ~ (v2_pre_topc @ X17)
% 0.90/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.90/1.13          | (v3_pre_topc @ (k1_tops_1 @ X17 @ X18) @ X17))),
% 0.90/1.13      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.90/1.13  thf('19', plain,
% 0.90/1.13      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.90/1.13        | ~ (v2_pre_topc @ sk_A)
% 0.90/1.13        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.13      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.13  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('22', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.90/1.13      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.90/1.13  thf('23', plain,
% 0.90/1.13      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.90/1.13         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)))
% 0.90/1.13         <= ((![X26 : $i]:
% 0.90/1.13                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.13                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.90/1.13                 | ~ (r1_tarski @ X26 @ sk_C_1)
% 0.90/1.13                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.90/1.13      inference('demod', [status(thm)], ['16', '22'])).
% 0.90/1.13  thf('24', plain,
% 0.90/1.13      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))
% 0.90/1.13         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))) & 
% 0.90/1.13             (![X26 : $i]:
% 0.90/1.13                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.13                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.90/1.13                 | ~ (r1_tarski @ X26 @ sk_C_1)
% 0.90/1.13                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['9', '23'])).
% 0.90/1.13  thf('25', plain,
% 0.90/1.13      (~
% 0.90/1.13       (![X26 : $i]:
% 0.90/1.13          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.13           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.90/1.13           | ~ (r1_tarski @ X26 @ sk_C_1)
% 0.90/1.13           | ~ (r2_hidden @ sk_B @ X26))) | 
% 0.90/1.13       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['7', '24'])).
% 0.90/1.13  thf('26', plain, (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.13      inference('sat_resolution*', [status(thm)], ['2', '25'])).
% 0.90/1.13  thf('27', plain, (~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.90/1.13      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.90/1.13  thf('28', plain,
% 0.90/1.13      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.90/1.13      inference('split', [status(esa)], ['8'])).
% 0.90/1.13  thf('29', plain,
% 0.90/1.13      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.90/1.13       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.13      inference('split', [status(esa)], ['8'])).
% 0.90/1.13  thf('30', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.90/1.13      inference('sat_resolution*', [status(thm)], ['2', '25', '29'])).
% 0.90/1.13  thf('31', plain, ((r2_hidden @ sk_B @ sk_D)),
% 0.90/1.13      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 0.90/1.13  thf('32', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('33', plain,
% 0.90/1.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.13        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('34', plain,
% 0.90/1.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.90/1.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.13      inference('split', [status(esa)], ['33'])).
% 0.90/1.13  thf('35', plain,
% 0.90/1.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.90/1.13       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.13      inference('split', [status(esa)], ['33'])).
% 0.90/1.13  thf('36', plain,
% 0.90/1.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.13      inference('sat_resolution*', [status(thm)], ['2', '25', '35'])).
% 0.90/1.13  thf('37', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.13      inference('simpl_trail', [status(thm)], ['34', '36'])).
% 0.90/1.13  thf(t48_tops_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.13           ( ![C:$i]:
% 0.90/1.13             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.13               ( ( r1_tarski @ B @ C ) =>
% 0.90/1.13                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.90/1.13  thf('38', plain,
% 0.90/1.13      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.90/1.13          | ~ (r1_tarski @ X23 @ X25)
% 0.90/1.13          | (r1_tarski @ (k1_tops_1 @ X24 @ X23) @ (k1_tops_1 @ X24 @ X25))
% 0.90/1.13          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.90/1.13          | ~ (l1_pre_topc @ X24))),
% 0.90/1.13      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.90/1.13  thf('39', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ sk_A)
% 0.90/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.13          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.90/1.13          | ~ (r1_tarski @ sk_D @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.13  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('41', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.13          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.90/1.13          | ~ (r1_tarski @ sk_D @ X0))),
% 0.90/1.13      inference('demod', [status(thm)], ['39', '40'])).
% 0.90/1.13  thf('42', plain,
% 0.90/1.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.90/1.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.13      inference('split', [status(esa)], ['33'])).
% 0.90/1.13  thf(d1_tops_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.13           ( ( k1_tops_1 @ A @ B ) =
% 0.90/1.13             ( k3_subset_1 @
% 0.90/1.13               ( u1_struct_0 @ A ) @ 
% 0.90/1.13               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.90/1.13  thf('43', plain,
% 0.90/1.13      (![X13 : $i, X14 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.90/1.13          | ((k1_tops_1 @ X14 @ X13)
% 0.90/1.13              = (k3_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.90/1.13                 (k2_pre_topc @ X14 @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13))))
% 0.90/1.13          | ~ (l1_pre_topc @ X14))),
% 0.90/1.13      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.90/1.13  thf('44', plain,
% 0.90/1.13      (((~ (l1_pre_topc @ sk_A)
% 0.90/1.13         | ((k1_tops_1 @ sk_A @ sk_D)
% 0.90/1.13             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.13                (k2_pre_topc @ sk_A @ 
% 0.90/1.13                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))))
% 0.90/1.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['42', '43'])).
% 0.90/1.13  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('46', plain,
% 0.90/1.13      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.90/1.13          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.13             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))))
% 0.90/1.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.13      inference('demod', [status(thm)], ['44', '45'])).
% 0.90/1.13  thf('47', plain,
% 0.90/1.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.90/1.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.13      inference('split', [status(esa)], ['33'])).
% 0.90/1.13  thf(dt_k3_subset_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.13       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.90/1.13  thf('48', plain,
% 0.90/1.13      (![X4 : $i, X5 : $i]:
% 0.90/1.13         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.90/1.13          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.90/1.13  thf('49', plain,
% 0.90/1.13      (((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.90/1.14         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.90/1.14         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['47', '48'])).
% 0.90/1.14  thf('50', plain,
% 0.90/1.14      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.14      inference('sat_resolution*', [status(thm)], ['2', '25', '35'])).
% 0.90/1.14  thf('51', plain,
% 0.90/1.14      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.90/1.14        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.14      inference('simpl_trail', [status(thm)], ['49', '50'])).
% 0.90/1.14  thf(t52_pre_topc, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( l1_pre_topc @ A ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.14           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.90/1.14             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.90/1.14               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.90/1.14  thf('52', plain,
% 0.90/1.14      (![X11 : $i, X12 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.90/1.14          | ~ (v4_pre_topc @ X11 @ X12)
% 0.90/1.14          | ((k2_pre_topc @ X12 @ X11) = (X11))
% 0.90/1.14          | ~ (l1_pre_topc @ X12))),
% 0.90/1.14      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.90/1.14  thf('53', plain,
% 0.90/1.14      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.14        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.90/1.14            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.90/1.14        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A))),
% 0.90/1.14      inference('sup-', [status(thm)], ['51', '52'])).
% 0.90/1.14  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('55', plain,
% 0.90/1.14      (((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.90/1.14         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.90/1.14         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['47', '48'])).
% 0.90/1.14  thf(t29_tops_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( l1_pre_topc @ A ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.14           ( ( v4_pre_topc @ B @ A ) <=>
% 0.90/1.14             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.90/1.14  thf('56', plain,
% 0.90/1.14      (![X19 : $i, X20 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.90/1.14          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.90/1.14          | (v4_pre_topc @ X19 @ X20)
% 0.90/1.14          | ~ (l1_pre_topc @ X20))),
% 0.90/1.14      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.90/1.14  thf('57', plain,
% 0.90/1.14      (((~ (l1_pre_topc @ sk_A)
% 0.90/1.14         | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.90/1.14         | ~ (v3_pre_topc @ 
% 0.90/1.14              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) @ 
% 0.90/1.14              sk_A)))
% 0.90/1.14         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['55', '56'])).
% 0.90/1.14  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('59', plain,
% 0.90/1.14      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.90/1.14         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.14      inference('split', [status(esa)], ['33'])).
% 0.90/1.14  thf(involutiveness_k3_subset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.14       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.90/1.14  thf('60', plain,
% 0.90/1.14      (![X6 : $i, X7 : $i]:
% 0.90/1.14         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.90/1.14          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.90/1.14      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.90/1.14  thf('61', plain,
% 0.90/1.14      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 0.90/1.14         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['59', '60'])).
% 0.90/1.14  thf('62', plain,
% 0.90/1.14      ((((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.90/1.14         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.90/1.14         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.14      inference('demod', [status(thm)], ['57', '58', '61'])).
% 0.90/1.14  thf('63', plain,
% 0.90/1.14      (((v3_pre_topc @ sk_D @ sk_A)
% 0.90/1.14        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('64', plain,
% 0.90/1.14      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.90/1.14      inference('split', [status(esa)], ['63'])).
% 0.90/1.14  thf('65', plain,
% 0.90/1.14      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.90/1.14       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.14      inference('split', [status(esa)], ['63'])).
% 0.90/1.14  thf('66', plain, (((v3_pre_topc @ sk_D @ sk_A))),
% 0.90/1.14      inference('sat_resolution*', [status(thm)], ['2', '25', '65'])).
% 0.90/1.14  thf('67', plain, ((v3_pre_topc @ sk_D @ sk_A)),
% 0.90/1.14      inference('simpl_trail', [status(thm)], ['64', '66'])).
% 0.90/1.14  thf('68', plain,
% 0.90/1.14      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A))
% 0.90/1.14         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.14      inference('demod', [status(thm)], ['62', '67'])).
% 0.90/1.14  thf('69', plain,
% 0.90/1.14      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.14      inference('sat_resolution*', [status(thm)], ['2', '25', '35'])).
% 0.90/1.14  thf('70', plain,
% 0.90/1.14      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)),
% 0.90/1.14      inference('simpl_trail', [status(thm)], ['68', '69'])).
% 0.90/1.14  thf('71', plain,
% 0.90/1.14      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.90/1.14         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['53', '54', '70'])).
% 0.90/1.14  thf('72', plain,
% 0.90/1.14      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.90/1.14          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))
% 0.90/1.14         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.14      inference('demod', [status(thm)], ['46', '71'])).
% 0.90/1.14  thf('73', plain,
% 0.90/1.14      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.14      inference('sat_resolution*', [status(thm)], ['2', '25', '35'])).
% 0.90/1.14  thf('74', plain,
% 0.90/1.14      (((k1_tops_1 @ sk_A @ sk_D)
% 0.90/1.14         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.90/1.14      inference('simpl_trail', [status(thm)], ['72', '73'])).
% 0.90/1.14  thf('75', plain,
% 0.90/1.14      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 0.90/1.14         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['59', '60'])).
% 0.90/1.14  thf('76', plain,
% 0.90/1.14      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.14      inference('sat_resolution*', [status(thm)], ['2', '25', '35'])).
% 0.90/1.14  thf('77', plain,
% 0.90/1.14      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D))),
% 0.90/1.14      inference('simpl_trail', [status(thm)], ['75', '76'])).
% 0.90/1.14  thf('78', plain, (((k1_tops_1 @ sk_A @ sk_D) = (sk_D))),
% 0.90/1.14      inference('sup+', [status(thm)], ['74', '77'])).
% 0.90/1.14  thf('79', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.14          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ X0))
% 0.90/1.14          | ~ (r1_tarski @ sk_D @ X0))),
% 0.90/1.14      inference('demod', [status(thm)], ['41', '78'])).
% 0.90/1.14  thf('80', plain,
% 0.90/1.14      ((~ (r1_tarski @ sk_D @ sk_C_1)
% 0.90/1.14        | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['32', '79'])).
% 0.90/1.14  thf('81', plain,
% 0.90/1.14      (((r1_tarski @ sk_D @ sk_C_1)
% 0.90/1.14        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('82', plain,
% 0.90/1.14      (((r1_tarski @ sk_D @ sk_C_1)) <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.90/1.14      inference('split', [status(esa)], ['81'])).
% 0.90/1.14  thf('83', plain,
% 0.90/1.14      (((r1_tarski @ sk_D @ sk_C_1)) | 
% 0.90/1.14       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.14      inference('split', [status(esa)], ['81'])).
% 0.90/1.14  thf('84', plain, (((r1_tarski @ sk_D @ sk_C_1))),
% 0.90/1.14      inference('sat_resolution*', [status(thm)], ['2', '25', '83'])).
% 0.90/1.14  thf('85', plain, ((r1_tarski @ sk_D @ sk_C_1)),
% 0.90/1.14      inference('simpl_trail', [status(thm)], ['82', '84'])).
% 0.90/1.14  thf('86', plain, ((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.90/1.14      inference('demod', [status(thm)], ['80', '85'])).
% 0.90/1.14  thf(d3_tarski, axiom,
% 0.90/1.14    (![A:$i,B:$i]:
% 0.90/1.14     ( ( r1_tarski @ A @ B ) <=>
% 0.90/1.14       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.90/1.14  thf('87', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X0 @ X1)
% 0.90/1.14          | (r2_hidden @ X0 @ X2)
% 0.90/1.14          | ~ (r1_tarski @ X1 @ X2))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.14  thf('88', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.90/1.14          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['86', '87'])).
% 0.90/1.14  thf('89', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.90/1.14      inference('sup-', [status(thm)], ['31', '88'])).
% 0.90/1.14  thf('90', plain, ($false), inference('demod', [status(thm)], ['27', '89'])).
% 0.90/1.14  
% 0.90/1.14  % SZS output end Refutation
% 0.90/1.14  
% 0.90/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
