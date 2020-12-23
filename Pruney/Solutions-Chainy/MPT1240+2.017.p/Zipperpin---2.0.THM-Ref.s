%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KB2jcNXhX4

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:08 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 170 expanded)
%              Number of leaves         :   28 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          : 1133 (2765 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X25 @ sk_A )
      | ~ ( r1_tarski @ X25 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X25 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X25 ) )
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
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X16 @ X17 ) @ X16 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
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
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X25 ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X25 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('21',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X25 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X21 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X25 ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
   <= ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      & ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X25 @ sk_A )
          | ~ ( r1_tarski @ X25 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X25 ) ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,
    ( ~ ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X25 @ sk_A )
          | ~ ( r1_tarski @ X25 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X25 ) )
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
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['30'])).

thf('34',plain,
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

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('36',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

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

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X11 )
      | ( ( k2_pre_topc @ X11 @ X10 )
        = X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('44',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,
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

thf('49',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k1_tops_1 @ X13 @ X12 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k2_pre_topc @ X13 @ ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('50',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_D )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('56',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = sk_D )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
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

thf('61',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ( r1_tarski @ ( k1_tops_1 @ X23 @ X22 ) @ ( k1_tops_1 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['57','66'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('68',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('70',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','71'])).

thf('73',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('74',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_D @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','29','31','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KB2jcNXhX4
% 0.15/0.38  % Computer   : n007.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 17:13:36 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.45/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.61  % Solved by: fo/fo7.sh
% 0.45/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.61  % done 306 iterations in 0.116s
% 0.45/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.61  % SZS output start Refutation
% 0.45/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.45/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.61  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.45/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.45/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.61  thf(t54_tops_1, conjecture,
% 0.45/0.61    (![A:$i]:
% 0.45/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.61       ( ![B:$i,C:$i]:
% 0.45/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.61           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.45/0.61             ( ?[D:$i]:
% 0.45/0.61               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.45/0.61                 ( v3_pre_topc @ D @ A ) & 
% 0.45/0.61                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.61    (~( ![A:$i]:
% 0.45/0.61        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.61          ( ![B:$i,C:$i]:
% 0.45/0.61            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.61              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.45/0.61                ( ?[D:$i]:
% 0.45/0.61                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.45/0.61                    ( v3_pre_topc @ D @ A ) & 
% 0.45/0.61                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.45/0.61    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 0.45/0.61  thf('0', plain,
% 0.45/0.61      (((r2_hidden @ sk_B @ sk_D)
% 0.45/0.61        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('1', plain,
% 0.45/0.61      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.45/0.61       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.61      inference('split', [status(esa)], ['0'])).
% 0.45/0.61  thf('2', plain,
% 0.45/0.61      (((r1_tarski @ sk_D @ sk_C)
% 0.45/0.61        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('3', plain,
% 0.45/0.61      (((r1_tarski @ sk_D @ sk_C)) | 
% 0.45/0.61       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.61      inference('split', [status(esa)], ['2'])).
% 0.45/0.61  thf('4', plain,
% 0.45/0.61      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.61        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('5', plain,
% 0.45/0.61      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.45/0.61       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.61      inference('split', [status(esa)], ['4'])).
% 0.45/0.61  thf('6', plain,
% 0.45/0.61      (![X25 : $i]:
% 0.45/0.61         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.61          | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.45/0.61          | ~ (r1_tarski @ X25 @ sk_C)
% 0.45/0.61          | ~ (r2_hidden @ sk_B @ X25)
% 0.45/0.61          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('7', plain,
% 0.45/0.61      ((![X25 : $i]:
% 0.45/0.61          (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.61           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.45/0.61           | ~ (r1_tarski @ X25 @ sk_C)
% 0.45/0.61           | ~ (r2_hidden @ sk_B @ X25))) | 
% 0.45/0.61       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.61      inference('split', [status(esa)], ['6'])).
% 0.45/0.61  thf('8', plain,
% 0.45/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf(fc9_tops_1, axiom,
% 0.45/0.61    (![A:$i,B:$i]:
% 0.45/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.45/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.61       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.45/0.61  thf('9', plain,
% 0.45/0.61      (![X16 : $i, X17 : $i]:
% 0.45/0.61         (~ (l1_pre_topc @ X16)
% 0.45/0.61          | ~ (v2_pre_topc @ X16)
% 0.45/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.45/0.61          | (v3_pre_topc @ (k1_tops_1 @ X16 @ X17) @ X16))),
% 0.45/0.61      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.45/0.61  thf('10', plain,
% 0.45/0.61      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.45/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.61  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('13', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.45/0.61      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.45/0.61  thf('14', plain,
% 0.45/0.61      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.45/0.61         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.45/0.61      inference('split', [status(esa)], ['0'])).
% 0.45/0.61  thf('15', plain,
% 0.45/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf(dt_k1_tops_1, axiom,
% 0.45/0.61    (![A:$i,B:$i]:
% 0.45/0.61     ( ( ( l1_pre_topc @ A ) & 
% 0.45/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.61       ( m1_subset_1 @
% 0.45/0.61         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.61  thf('16', plain,
% 0.45/0.61      (![X14 : $i, X15 : $i]:
% 0.45/0.61         (~ (l1_pre_topc @ X14)
% 0.45/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.45/0.61          | (m1_subset_1 @ (k1_tops_1 @ X14 @ X15) @ 
% 0.45/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.45/0.61      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.45/0.61  thf('17', plain,
% 0.45/0.61      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.45/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.61  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('19', plain,
% 0.45/0.61      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.45/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.61  thf('20', plain,
% 0.45/0.61      ((![X25 : $i]:
% 0.45/0.61          (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.61           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.45/0.61           | ~ (r1_tarski @ X25 @ sk_C)
% 0.45/0.61           | ~ (r2_hidden @ sk_B @ X25)))
% 0.45/0.61         <= ((![X25 : $i]:
% 0.45/0.61                (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.61                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.45/0.61                 | ~ (r1_tarski @ X25 @ sk_C)
% 0.45/0.61                 | ~ (r2_hidden @ sk_B @ X25))))),
% 0.45/0.61      inference('split', [status(esa)], ['6'])).
% 0.45/0.61  thf('21', plain,
% 0.45/0.61      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.45/0.61         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.45/0.61         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.45/0.61         <= ((![X25 : $i]:
% 0.45/0.61                (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.61                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.45/0.61                 | ~ (r1_tarski @ X25 @ sk_C)
% 0.45/0.61                 | ~ (r2_hidden @ sk_B @ X25))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.61  thf('22', plain,
% 0.45/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf(t44_tops_1, axiom,
% 0.45/0.61    (![A:$i]:
% 0.45/0.61     ( ( l1_pre_topc @ A ) =>
% 0.45/0.61       ( ![B:$i]:
% 0.45/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.61           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.45/0.61  thf('23', plain,
% 0.45/0.61      (![X20 : $i, X21 : $i]:
% 0.45/0.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.61          | (r1_tarski @ (k1_tops_1 @ X21 @ X20) @ X20)
% 0.45/0.61          | ~ (l1_pre_topc @ X21))),
% 0.45/0.61      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.45/0.61  thf('24', plain,
% 0.45/0.61      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.45/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.61  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('26', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.45/0.61      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.61  thf('27', plain,
% 0.45/0.61      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.45/0.61         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.45/0.61         <= ((![X25 : $i]:
% 0.45/0.61                (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.61                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.45/0.61                 | ~ (r1_tarski @ X25 @ sk_C)
% 0.45/0.61                 | ~ (r2_hidden @ sk_B @ X25))))),
% 0.45/0.61      inference('demod', [status(thm)], ['21', '26'])).
% 0.45/0.61  thf('28', plain,
% 0.45/0.61      ((~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A))
% 0.45/0.61         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) & 
% 0.45/0.61             (![X25 : $i]:
% 0.45/0.61                (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.61                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.45/0.61                 | ~ (r1_tarski @ X25 @ sk_C)
% 0.45/0.61                 | ~ (r2_hidden @ sk_B @ X25))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['14', '27'])).
% 0.45/0.61  thf('29', plain,
% 0.45/0.61      (~
% 0.45/0.61       (![X25 : $i]:
% 0.45/0.61          (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.61           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.45/0.61           | ~ (r1_tarski @ X25 @ sk_C)
% 0.45/0.61           | ~ (r2_hidden @ sk_B @ X25))) | 
% 0.45/0.61       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.61      inference('sup-', [status(thm)], ['13', '28'])).
% 0.45/0.61  thf('30', plain,
% 0.45/0.61      (((v3_pre_topc @ sk_D @ sk_A)
% 0.45/0.61        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('31', plain,
% 0.45/0.61      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.45/0.61       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.61      inference('split', [status(esa)], ['30'])).
% 0.45/0.61  thf('32', plain,
% 0.45/0.61      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.45/0.61      inference('split', [status(esa)], ['0'])).
% 0.45/0.61  thf('33', plain,
% 0.45/0.61      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.45/0.61      inference('split', [status(esa)], ['30'])).
% 0.45/0.61  thf('34', plain,
% 0.45/0.61      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('split', [status(esa)], ['4'])).
% 0.45/0.61  thf(t30_tops_1, axiom,
% 0.45/0.61    (![A:$i]:
% 0.45/0.61     ( ( l1_pre_topc @ A ) =>
% 0.45/0.61       ( ![B:$i]:
% 0.45/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.61           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.61             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.45/0.61  thf('35', plain,
% 0.45/0.61      (![X18 : $i, X19 : $i]:
% 0.45/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.61          | ~ (v3_pre_topc @ X18 @ X19)
% 0.45/0.61          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X19) @ X18) @ X19)
% 0.45/0.61          | ~ (l1_pre_topc @ X19))),
% 0.45/0.61      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.45/0.61  thf('36', plain,
% 0.45/0.61      (((~ (l1_pre_topc @ sk_A)
% 0.45/0.61         | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.45/0.61         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.61  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('38', plain,
% 0.45/0.61      ((((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.45/0.61         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.61  thf('39', plain,
% 0.45/0.61      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A))
% 0.45/0.61         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.61             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['33', '38'])).
% 0.45/0.61  thf('40', plain,
% 0.45/0.61      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('split', [status(esa)], ['4'])).
% 0.45/0.61  thf(dt_k3_subset_1, axiom,
% 0.45/0.61    (![A:$i,B:$i]:
% 0.45/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.61       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.61  thf('41', plain,
% 0.45/0.61      (![X0 : $i, X1 : $i]:
% 0.45/0.61         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.45/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.45/0.61      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.45/0.61  thf('42', plain,
% 0.45/0.61      (((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.45/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.61  thf(t52_pre_topc, axiom,
% 0.45/0.61    (![A:$i]:
% 0.45/0.61     ( ( l1_pre_topc @ A ) =>
% 0.45/0.61       ( ![B:$i]:
% 0.45/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.61           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.45/0.61             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.45/0.61               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.45/0.61  thf('43', plain,
% 0.45/0.61      (![X10 : $i, X11 : $i]:
% 0.45/0.61         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.45/0.61          | ~ (v4_pre_topc @ X10 @ X11)
% 0.45/0.61          | ((k2_pre_topc @ X11 @ X10) = (X10))
% 0.45/0.61          | ~ (l1_pre_topc @ X11))),
% 0.45/0.61      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.45/0.61  thf('44', plain,
% 0.45/0.61      (((~ (l1_pre_topc @ sk_A)
% 0.45/0.61         | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.45/0.61             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.45/0.61         | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.61  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('46', plain,
% 0.45/0.61      (((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.45/0.61           = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.45/0.61         | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.61  thf('47', plain,
% 0.45/0.61      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.45/0.61          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.45/0.61         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.61             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['39', '46'])).
% 0.45/0.61  thf('48', plain,
% 0.45/0.61      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('split', [status(esa)], ['4'])).
% 0.45/0.61  thf(d1_tops_1, axiom,
% 0.45/0.61    (![A:$i]:
% 0.45/0.61     ( ( l1_pre_topc @ A ) =>
% 0.45/0.61       ( ![B:$i]:
% 0.45/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.61           ( ( k1_tops_1 @ A @ B ) =
% 0.45/0.61             ( k3_subset_1 @
% 0.45/0.61               ( u1_struct_0 @ A ) @ 
% 0.45/0.61               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.45/0.61  thf('49', plain,
% 0.45/0.61      (![X12 : $i, X13 : $i]:
% 0.45/0.61         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.45/0.61          | ((k1_tops_1 @ X13 @ X12)
% 0.45/0.61              = (k3_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.45/0.61                 (k2_pre_topc @ X13 @ (k3_subset_1 @ (u1_struct_0 @ X13) @ X12))))
% 0.45/0.61          | ~ (l1_pre_topc @ X13))),
% 0.45/0.61      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.45/0.61  thf('50', plain,
% 0.45/0.61      (((~ (l1_pre_topc @ sk_A)
% 0.45/0.61         | ((k1_tops_1 @ sk_A @ sk_D)
% 0.45/0.61             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.61                (k2_pre_topc @ sk_A @ 
% 0.45/0.61                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.61  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('52', plain,
% 0.45/0.61      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.45/0.61          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.61             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.61  thf('53', plain,
% 0.45/0.61      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.45/0.61          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.61             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))
% 0.45/0.61         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.61             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup+', [status(thm)], ['47', '52'])).
% 0.45/0.61  thf('54', plain,
% 0.45/0.61      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('split', [status(esa)], ['4'])).
% 0.45/0.61  thf(involutiveness_k3_subset_1, axiom,
% 0.45/0.61    (![A:$i,B:$i]:
% 0.45/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.61       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.45/0.61  thf('55', plain,
% 0.45/0.61      (![X2 : $i, X3 : $i]:
% 0.45/0.61         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.45/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.45/0.61      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.45/0.61  thf('56', plain,
% 0.45/0.61      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.61          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.61  thf('57', plain,
% 0.45/0.61      ((((k1_tops_1 @ sk_A @ sk_D) = (sk_D)))
% 0.45/0.61         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.61             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup+', [status(thm)], ['53', '56'])).
% 0.45/0.61  thf('58', plain,
% 0.45/0.61      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.45/0.61      inference('split', [status(esa)], ['2'])).
% 0.45/0.61  thf('59', plain,
% 0.45/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('60', plain,
% 0.45/0.61      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('split', [status(esa)], ['4'])).
% 0.45/0.61  thf(t48_tops_1, axiom,
% 0.45/0.61    (![A:$i]:
% 0.45/0.61     ( ( l1_pre_topc @ A ) =>
% 0.45/0.61       ( ![B:$i]:
% 0.45/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.61           ( ![C:$i]:
% 0.45/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.61               ( ( r1_tarski @ B @ C ) =>
% 0.45/0.61                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.45/0.61  thf('61', plain,
% 0.45/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.61         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.45/0.61          | ~ (r1_tarski @ X22 @ X24)
% 0.45/0.61          | (r1_tarski @ (k1_tops_1 @ X23 @ X22) @ (k1_tops_1 @ X23 @ X24))
% 0.45/0.61          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.45/0.61          | ~ (l1_pre_topc @ X23))),
% 0.45/0.61      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.45/0.61  thf('62', plain,
% 0.45/0.61      ((![X0 : $i]:
% 0.45/0.61          (~ (l1_pre_topc @ sk_A)
% 0.45/0.61           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.61           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.45/0.61           | ~ (r1_tarski @ sk_D @ X0)))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['60', '61'])).
% 0.45/0.61  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('64', plain,
% 0.45/0.61      ((![X0 : $i]:
% 0.45/0.61          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.61           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.45/0.61           | ~ (r1_tarski @ sk_D @ X0)))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('demod', [status(thm)], ['62', '63'])).
% 0.45/0.61  thf('65', plain,
% 0.45/0.61      (((~ (r1_tarski @ sk_D @ sk_C)
% 0.45/0.61         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.45/0.61         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['59', '64'])).
% 0.45/0.61  thf('66', plain,
% 0.45/0.61      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.45/0.61         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.61             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['58', '65'])).
% 0.45/0.61  thf('67', plain,
% 0.45/0.61      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.45/0.61         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.61             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.61             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup+', [status(thm)], ['57', '66'])).
% 0.45/0.61  thf(t3_subset, axiom,
% 0.45/0.61    (![A:$i,B:$i]:
% 0.45/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.61  thf('68', plain,
% 0.45/0.61      (![X7 : $i, X9 : $i]:
% 0.45/0.61         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.45/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.61  thf('69', plain,
% 0.45/0.61      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.45/0.61         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.61             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.61             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['67', '68'])).
% 0.45/0.61  thf(l3_subset_1, axiom,
% 0.45/0.61    (![A:$i,B:$i]:
% 0.45/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.45/0.61  thf('70', plain,
% 0.45/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.61         (~ (r2_hidden @ X4 @ X5)
% 0.45/0.61          | (r2_hidden @ X4 @ X6)
% 0.45/0.61          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.45/0.61      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.45/0.61  thf('71', plain,
% 0.45/0.61      ((![X0 : $i]:
% 0.45/0.61          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.45/0.61           | ~ (r2_hidden @ X0 @ sk_D)))
% 0.45/0.61         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.61             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.61             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.61  thf('72', plain,
% 0.45/0.61      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.45/0.61         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.45/0.61             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.45/0.61             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.45/0.61             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['32', '71'])).
% 0.45/0.61  thf('73', plain,
% 0.45/0.61      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.45/0.61         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.45/0.61      inference('split', [status(esa)], ['6'])).
% 0.45/0.61  thf('74', plain,
% 0.45/0.61      (~ ((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.45/0.61       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.45/0.61       ~ ((r1_tarski @ sk_D @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_D)) | 
% 0.45/0.61       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.45/0.61      inference('sup-', [status(thm)], ['72', '73'])).
% 0.45/0.61  thf('75', plain, ($false),
% 0.45/0.61      inference('sat_resolution*', [status(thm)],
% 0.45/0.61                ['1', '3', '5', '7', '29', '31', '74'])).
% 0.45/0.61  
% 0.45/0.61  % SZS output end Refutation
% 0.45/0.61  
% 0.45/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
