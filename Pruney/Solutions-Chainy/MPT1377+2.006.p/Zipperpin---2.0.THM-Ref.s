%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bwJtbnT8me

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:45 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 412 expanded)
%              Number of leaves         :   26 ( 126 expanded)
%              Depth                    :   17
%              Number of atoms          : 2026 (6767 expanded)
%              Number of equality atoms :   28 (  92 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(t33_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_compts_1 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v2_compts_1 @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_compts_1 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
          <=> ( ( v2_compts_1 @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_compts_1])).

thf('0',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
    | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X5 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('10',plain,
    ( ( ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('15',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t28_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( C = D )
                   => ( ( v2_compts_1 @ C @ A )
                    <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_compts_1 @ X19 @ X17 )
      | ( v2_compts_1 @ X18 @ X16 )
      | ( X19 != X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_compts_1])).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_compts_1 @ X18 @ X16 )
      | ~ ( v2_compts_1 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v2_compts_1 @ sk_B @ X0 ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v2_compts_1 @ sk_B @ X0 ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) ) ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('26',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X13 @ X12 ) )
        = X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('28',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
        = sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
        = sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      = sk_B )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('32',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('34',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['24','31','34'])).

thf('36',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      = sk_B )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('37',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('41',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( ( g1_pre_topc @ X10 @ X11 )
       != ( g1_pre_topc @ X8 @ X9 ) )
      | ( X10 = X8 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf('50',plain,
    ( ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_compts_1 @ X18 @ X16 )
      | ( v2_compts_1 @ X19 @ X17 )
      | ( X19 != X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_compts_1])).

thf('54',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_compts_1 @ X18 @ X17 )
      | ~ ( v2_compts_1 @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ X0 )
        | ( v2_compts_1 @ sk_B @ sk_A )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ X0 )
        | ( v2_compts_1 @ sk_B @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['36','57'])).

thf('59',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('60',plain,
    ( ( ( v2_compts_1 @ sk_B @ sk_A )
      | ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ( m1_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('63',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ sk_A )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( v2_compts_1 @ sk_B @ sk_A )
      | ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('67',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['35','66'])).

thf('68',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
   <= ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('69',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('71',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      = sk_B )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('74',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('76',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_compts_1 @ X18 @ X16 )
      | ~ ( v2_compts_1 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ sk_A )
        | ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ sk_A )
        | ( v2_compts_1 @ sk_B @ X0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ sk_A )
      | ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['73','80'])).

thf('82',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('83',plain,
    ( ( ~ ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ sk_A )
      | ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ sk_A )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('85',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf('89',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_compts_1 @ X18 @ X17 )
      | ~ ( v2_compts_1 @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ X0 )
        | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) ) )
      | ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('95',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      = sk_B )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('96',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('97',plain,
    ( ( ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['85','97'])).

thf('99',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('100',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['101'])).

thf('103',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('106',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('107',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','69','72','100','102','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bwJtbnT8me
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:08:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.91/1.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.13  % Solved by: fo/fo7.sh
% 0.91/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.13  % done 783 iterations in 0.681s
% 0.91/1.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.13  % SZS output start Refutation
% 0.91/1.13  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.91/1.13  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.91/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.13  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.91/1.13  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.91/1.13  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.91/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.13  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.91/1.13  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.91/1.13  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.91/1.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.13  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.91/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.13  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.91/1.13  thf(t33_compts_1, conjecture,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.13       ( ![B:$i]:
% 0.91/1.13         ( ( ( v2_compts_1 @ B @ A ) & 
% 0.91/1.13             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.91/1.13           ( ( v2_compts_1 @
% 0.91/1.13               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.91/1.13             ( m1_subset_1 @
% 0.91/1.13               B @ 
% 0.91/1.13               ( k1_zfmisc_1 @
% 0.91/1.13                 ( u1_struct_0 @
% 0.91/1.13                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.91/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.13    (~( ![A:$i]:
% 0.91/1.13        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.91/1.13            ( l1_pre_topc @ A ) ) =>
% 0.91/1.13          ( ![B:$i]:
% 0.91/1.13            ( ( ( v2_compts_1 @ B @ A ) & 
% 0.91/1.13                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.91/1.13              ( ( v2_compts_1 @
% 0.91/1.13                  B @ 
% 0.91/1.13                  ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.91/1.13                ( m1_subset_1 @
% 0.91/1.13                  B @ 
% 0.91/1.13                  ( k1_zfmisc_1 @
% 0.91/1.13                    ( u1_struct_0 @
% 0.91/1.13                      ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) )),
% 0.91/1.13    inference('cnf.neg', [status(esa)], [t33_compts_1])).
% 0.91/1.13  thf('0', plain,
% 0.91/1.13      (((v2_compts_1 @ sk_B @ 
% 0.91/1.13         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.91/1.13        | (v2_compts_1 @ sk_B @ sk_A))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('1', plain,
% 0.91/1.13      (((v2_compts_1 @ sk_B @ sk_A)) | 
% 0.91/1.13       ((v2_compts_1 @ sk_B @ 
% 0.91/1.13         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.91/1.13      inference('split', [status(esa)], ['0'])).
% 0.91/1.13  thf('2', plain,
% 0.91/1.13      ((~ (m1_subset_1 @ sk_B @ 
% 0.91/1.13           (k1_zfmisc_1 @ 
% 0.91/1.13            (u1_struct_0 @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.91/1.13        | ~ (v2_compts_1 @ sk_B @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.91/1.13        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13        | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('3', plain,
% 0.91/1.13      (~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 0.91/1.13       ~
% 0.91/1.13       ((v2_compts_1 @ sk_B @ 
% 0.91/1.13         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.91/1.13       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.91/1.13       ~
% 0.91/1.13       ((m1_subset_1 @ sk_B @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (u1_struct_0 @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.91/1.13      inference('split', [status(esa)], ['2'])).
% 0.91/1.13  thf(dt_u1_pre_topc, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( l1_pre_topc @ A ) =>
% 0.91/1.13       ( m1_subset_1 @
% 0.91/1.13         ( u1_pre_topc @ A ) @ 
% 0.91/1.13         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.91/1.13  thf('4', plain,
% 0.91/1.13      (![X7 : $i]:
% 0.91/1.13         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.91/1.13           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.91/1.13          | ~ (l1_pre_topc @ X7))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.91/1.13  thf(dt_g1_pre_topc, axiom,
% 0.91/1.13    (![A:$i,B:$i]:
% 0.91/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.91/1.13       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.91/1.13         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.91/1.13  thf('5', plain,
% 0.91/1.13      (![X3 : $i, X4 : $i]:
% 0.91/1.13         ((l1_pre_topc @ (g1_pre_topc @ X3 @ X4))
% 0.91/1.13          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.91/1.13  thf('6', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X0)
% 0.91/1.13          | (l1_pre_topc @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.13  thf('7', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_B @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (u1_struct_0 @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.91/1.13        | (v2_compts_1 @ sk_B @ sk_A))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('8', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_B @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (u1_struct_0 @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('split', [status(esa)], ['7'])).
% 0.91/1.13  thf(dt_k1_pre_topc, axiom,
% 0.91/1.13    (![A:$i,B:$i]:
% 0.91/1.13     ( ( ( l1_pre_topc @ A ) & 
% 0.91/1.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.13       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.91/1.13         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.91/1.13  thf('9', plain,
% 0.91/1.13      (![X5 : $i, X6 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X5)
% 0.91/1.13          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.91/1.13          | (m1_pre_topc @ (k1_pre_topc @ X5 @ X6) @ X5))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.91/1.13  thf('10', plain,
% 0.91/1.13      ((((m1_pre_topc @ 
% 0.91/1.13          (k1_pre_topc @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 0.91/1.13          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.91/1.13         | ~ (l1_pre_topc @ 
% 0.91/1.13              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['8', '9'])).
% 0.91/1.13  thf('11', plain,
% 0.91/1.13      (((~ (l1_pre_topc @ sk_A)
% 0.91/1.13         | (m1_pre_topc @ 
% 0.91/1.13            (k1_pre_topc @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 0.91/1.13            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['6', '10'])).
% 0.91/1.13  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('13', plain,
% 0.91/1.13      (((m1_pre_topc @ 
% 0.91/1.13         (k1_pre_topc @ 
% 0.91/1.13          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 0.91/1.13         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['11', '12'])).
% 0.91/1.13  thf('14', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X0)
% 0.91/1.13          | (l1_pre_topc @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.13  thf('15', plain,
% 0.91/1.13      (((v2_compts_1 @ sk_B @ 
% 0.91/1.13         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.91/1.13         <= (((v2_compts_1 @ sk_B @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.91/1.13      inference('split', [status(esa)], ['0'])).
% 0.91/1.13  thf('16', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_B @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (u1_struct_0 @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('split', [status(esa)], ['7'])).
% 0.91/1.13  thf(t28_compts_1, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( l1_pre_topc @ A ) =>
% 0.91/1.13       ( ![B:$i]:
% 0.91/1.13         ( ( m1_pre_topc @ B @ A ) =>
% 0.91/1.13           ( ![C:$i]:
% 0.91/1.13             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.13               ( ![D:$i]:
% 0.91/1.13                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.91/1.13                   ( ( ( C ) = ( D ) ) =>
% 0.91/1.13                     ( ( v2_compts_1 @ C @ A ) <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.91/1.13  thf('17', plain,
% 0.91/1.13      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.91/1.13         (~ (m1_pre_topc @ X16 @ X17)
% 0.91/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.91/1.13          | ~ (v2_compts_1 @ X19 @ X17)
% 0.91/1.13          | (v2_compts_1 @ X18 @ X16)
% 0.91/1.13          | ((X19) != (X18))
% 0.91/1.13          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.91/1.13          | ~ (l1_pre_topc @ X17))),
% 0.91/1.13      inference('cnf', [status(esa)], [t28_compts_1])).
% 0.91/1.13  thf('18', plain,
% 0.91/1.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X17)
% 0.91/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.91/1.13          | (v2_compts_1 @ X18 @ X16)
% 0.91/1.13          | ~ (v2_compts_1 @ X18 @ X17)
% 0.91/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.91/1.13          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.91/1.13      inference('simplify', [status(thm)], ['17'])).
% 0.91/1.13  thf('19', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (~ (m1_pre_topc @ X0 @ 
% 0.91/1.13              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.91/1.13           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.13           | ~ (v2_compts_1 @ sk_B @ 
% 0.91/1.13                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.91/1.13           | (v2_compts_1 @ sk_B @ X0)
% 0.91/1.13           | ~ (l1_pre_topc @ 
% 0.91/1.13                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['16', '18'])).
% 0.91/1.13  thf('20', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (~ (l1_pre_topc @ 
% 0.91/1.13              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.91/1.13           | (v2_compts_1 @ sk_B @ X0)
% 0.91/1.13           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.13           | ~ (m1_pre_topc @ X0 @ 
% 0.91/1.13                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.91/1.13         <= (((v2_compts_1 @ sk_B @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.91/1.13             ((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['15', '19'])).
% 0.91/1.13  thf('21', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (~ (l1_pre_topc @ sk_A)
% 0.91/1.13           | ~ (m1_pre_topc @ X0 @ 
% 0.91/1.13                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.91/1.13           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.13           | (v2_compts_1 @ sk_B @ X0)))
% 0.91/1.13         <= (((v2_compts_1 @ sk_B @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.91/1.13             ((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['14', '20'])).
% 0.91/1.13  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('23', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (~ (m1_pre_topc @ X0 @ 
% 0.91/1.13              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.91/1.13           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.13           | (v2_compts_1 @ sk_B @ X0)))
% 0.91/1.13         <= (((v2_compts_1 @ sk_B @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.91/1.13             ((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['21', '22'])).
% 0.91/1.13  thf('24', plain,
% 0.91/1.13      ((((v2_compts_1 @ sk_B @ 
% 0.91/1.13          (k1_pre_topc @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.91/1.13         | ~ (m1_subset_1 @ sk_B @ 
% 0.91/1.13              (k1_zfmisc_1 @ 
% 0.91/1.13               (u1_struct_0 @ 
% 0.91/1.13                (k1_pre_topc @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.91/1.13                 sk_B))))))
% 0.91/1.13         <= (((v2_compts_1 @ sk_B @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.91/1.13             ((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['13', '23'])).
% 0.91/1.13  thf('25', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X0)
% 0.91/1.13          | (l1_pre_topc @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.13  thf('26', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_B @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (u1_struct_0 @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('split', [status(esa)], ['7'])).
% 0.91/1.13  thf(t29_pre_topc, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( l1_pre_topc @ A ) =>
% 0.91/1.13       ( ![B:$i]:
% 0.91/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.13           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.91/1.13  thf('27', plain,
% 0.91/1.13      (![X12 : $i, X13 : $i]:
% 0.91/1.13         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.91/1.13          | ((u1_struct_0 @ (k1_pre_topc @ X13 @ X12)) = (X12))
% 0.91/1.13          | ~ (l1_pre_topc @ X13))),
% 0.91/1.13      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.91/1.13  thf('28', plain,
% 0.91/1.13      (((~ (l1_pre_topc @ 
% 0.91/1.13            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.91/1.13         | ((u1_struct_0 @ 
% 0.91/1.13             (k1_pre_topc @ 
% 0.91/1.13              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.91/1.13              sk_B))
% 0.91/1.13             = (sk_B))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['26', '27'])).
% 0.91/1.13  thf('29', plain,
% 0.91/1.13      (((~ (l1_pre_topc @ sk_A)
% 0.91/1.13         | ((u1_struct_0 @ 
% 0.91/1.13             (k1_pre_topc @ 
% 0.91/1.13              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.91/1.13              sk_B))
% 0.91/1.13             = (sk_B))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['25', '28'])).
% 0.91/1.13  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('31', plain,
% 0.91/1.13      ((((u1_struct_0 @ 
% 0.91/1.13          (k1_pre_topc @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.91/1.13          = (sk_B)))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['29', '30'])).
% 0.91/1.13  thf(dt_k2_subset_1, axiom,
% 0.91/1.13    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.91/1.13  thf('32', plain,
% 0.91/1.13      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.91/1.13  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.91/1.13  thf('33', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.91/1.13      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.91/1.13  thf('34', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.91/1.13      inference('demod', [status(thm)], ['32', '33'])).
% 0.91/1.13  thf('35', plain,
% 0.91/1.13      (((v2_compts_1 @ sk_B @ 
% 0.91/1.13         (k1_pre_topc @ 
% 0.91/1.13          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 0.91/1.13         <= (((v2_compts_1 @ sk_B @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.91/1.13             ((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['24', '31', '34'])).
% 0.91/1.13  thf('36', plain,
% 0.91/1.13      ((((u1_struct_0 @ 
% 0.91/1.13          (k1_pre_topc @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.91/1.13          = (sk_B)))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['29', '30'])).
% 0.91/1.13  thf('37', plain,
% 0.91/1.13      (![X7 : $i]:
% 0.91/1.13         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.91/1.13           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.91/1.13          | ~ (l1_pre_topc @ X7))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.91/1.13  thf('38', plain,
% 0.91/1.13      (![X3 : $i, X4 : $i]:
% 0.91/1.13         ((v1_pre_topc @ (g1_pre_topc @ X3 @ X4))
% 0.91/1.13          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.91/1.13  thf('39', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X0)
% 0.91/1.13          | (v1_pre_topc @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['37', '38'])).
% 0.91/1.13  thf(abstractness_v1_pre_topc, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( l1_pre_topc @ A ) =>
% 0.91/1.13       ( ( v1_pre_topc @ A ) =>
% 0.91/1.13         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.91/1.13  thf('40', plain,
% 0.91/1.13      (![X2 : $i]:
% 0.91/1.13         (~ (v1_pre_topc @ X2)
% 0.91/1.13          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.91/1.13          | ~ (l1_pre_topc @ X2))),
% 0.91/1.13      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.91/1.13  thf('41', plain,
% 0.91/1.13      (![X7 : $i]:
% 0.91/1.13         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.91/1.13           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.91/1.13          | ~ (l1_pre_topc @ X7))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.91/1.13  thf(free_g1_pre_topc, axiom,
% 0.91/1.13    (![A:$i,B:$i]:
% 0.91/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.91/1.13       ( ![C:$i,D:$i]:
% 0.91/1.13         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.91/1.13           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.91/1.13  thf('42', plain,
% 0.91/1.13      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.91/1.13         (((g1_pre_topc @ X10 @ X11) != (g1_pre_topc @ X8 @ X9))
% 0.91/1.13          | ((X10) = (X8))
% 0.91/1.13          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.91/1.13      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.91/1.13  thf('43', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X0)
% 0.91/1.13          | ((u1_struct_0 @ X0) = (X1))
% 0.91/1.13          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.91/1.13              != (g1_pre_topc @ X1 @ X2)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['41', '42'])).
% 0.91/1.13  thf('44', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.13         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.91/1.13          | ~ (l1_pre_topc @ X0)
% 0.91/1.13          | ~ (v1_pre_topc @ X0)
% 0.91/1.13          | ((u1_struct_0 @ X0) = (X2))
% 0.91/1.13          | ~ (l1_pre_topc @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['40', '43'])).
% 0.91/1.13  thf('45', plain,
% 0.91/1.13      (![X1 : $i, X2 : $i]:
% 0.91/1.13         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.91/1.13          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.91/1.13          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.91/1.13      inference('simplify', [status(thm)], ['44'])).
% 0.91/1.13  thf('46', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X0)
% 0.91/1.13          | ~ (l1_pre_topc @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.91/1.13          | ((u1_struct_0 @ 
% 0.91/1.13              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.91/1.13              = (u1_struct_0 @ X0)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['39', '45'])).
% 0.91/1.13  thf('47', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X0)
% 0.91/1.13          | (l1_pre_topc @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.13  thf('48', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (((u1_struct_0 @ 
% 0.91/1.13            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.91/1.13            = (u1_struct_0 @ X0))
% 0.91/1.13          | ~ (l1_pre_topc @ X0))),
% 0.91/1.13      inference('clc', [status(thm)], ['46', '47'])).
% 0.91/1.13  thf('49', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_B @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (u1_struct_0 @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('split', [status(esa)], ['7'])).
% 0.91/1.13  thf('50', plain,
% 0.91/1.13      ((((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13         | ~ (l1_pre_topc @ sk_A)))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup+', [status(thm)], ['48', '49'])).
% 0.91/1.13  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('52', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['50', '51'])).
% 0.91/1.13  thf('53', plain,
% 0.91/1.13      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.91/1.13         (~ (m1_pre_topc @ X16 @ X17)
% 0.91/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.91/1.13          | ~ (v2_compts_1 @ X18 @ X16)
% 0.91/1.13          | (v2_compts_1 @ X19 @ X17)
% 0.91/1.13          | ((X19) != (X18))
% 0.91/1.13          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.91/1.13          | ~ (l1_pre_topc @ X17))),
% 0.91/1.13      inference('cnf', [status(esa)], [t28_compts_1])).
% 0.91/1.13  thf('54', plain,
% 0.91/1.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X17)
% 0.91/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.91/1.13          | (v2_compts_1 @ X18 @ X17)
% 0.91/1.13          | ~ (v2_compts_1 @ X18 @ X16)
% 0.91/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.91/1.13          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.91/1.13      inference('simplify', [status(thm)], ['53'])).
% 0.91/1.13  thf('55', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (~ (m1_pre_topc @ X0 @ sk_A)
% 0.91/1.13           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.13           | ~ (v2_compts_1 @ sk_B @ X0)
% 0.91/1.13           | (v2_compts_1 @ sk_B @ sk_A)
% 0.91/1.13           | ~ (l1_pre_topc @ sk_A)))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['52', '54'])).
% 0.91/1.13  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('57', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (~ (m1_pre_topc @ X0 @ sk_A)
% 0.91/1.13           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.13           | ~ (v2_compts_1 @ sk_B @ X0)
% 0.91/1.13           | (v2_compts_1 @ sk_B @ sk_A)))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['55', '56'])).
% 0.91/1.13  thf('58', plain,
% 0.91/1.13      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))
% 0.91/1.13         | (v2_compts_1 @ sk_B @ sk_A)
% 0.91/1.13         | ~ (v2_compts_1 @ sk_B @ 
% 0.91/1.13              (k1_pre_topc @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.91/1.13               sk_B))
% 0.91/1.13         | ~ (m1_pre_topc @ 
% 0.91/1.13              (k1_pre_topc @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.91/1.13               sk_B) @ 
% 0.91/1.13              sk_A)))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['36', '57'])).
% 0.91/1.13  thf('59', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.91/1.13      inference('demod', [status(thm)], ['32', '33'])).
% 0.91/1.13  thf('60', plain,
% 0.91/1.13      ((((v2_compts_1 @ sk_B @ sk_A)
% 0.91/1.13         | ~ (v2_compts_1 @ sk_B @ 
% 0.91/1.13              (k1_pre_topc @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.91/1.13               sk_B))
% 0.91/1.13         | ~ (m1_pre_topc @ 
% 0.91/1.13              (k1_pre_topc @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.91/1.13               sk_B) @ 
% 0.91/1.13              sk_A)))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['58', '59'])).
% 0.91/1.13  thf('61', plain,
% 0.91/1.13      (((m1_pre_topc @ 
% 0.91/1.13         (k1_pre_topc @ 
% 0.91/1.13          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 0.91/1.13         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['11', '12'])).
% 0.91/1.13  thf(t59_pre_topc, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( l1_pre_topc @ A ) =>
% 0.91/1.13       ( ![B:$i]:
% 0.91/1.13         ( ( m1_pre_topc @
% 0.91/1.13             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.91/1.13           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.91/1.13  thf('62', plain,
% 0.91/1.13      (![X14 : $i, X15 : $i]:
% 0.91/1.13         (~ (m1_pre_topc @ X14 @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.91/1.13          | (m1_pre_topc @ X14 @ X15)
% 0.91/1.13          | ~ (l1_pre_topc @ X15))),
% 0.91/1.13      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.91/1.13  thf('63', plain,
% 0.91/1.13      (((~ (l1_pre_topc @ sk_A)
% 0.91/1.13         | (m1_pre_topc @ 
% 0.91/1.13            (k1_pre_topc @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 0.91/1.13            sk_A)))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['61', '62'])).
% 0.91/1.13  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('65', plain,
% 0.91/1.13      (((m1_pre_topc @ 
% 0.91/1.13         (k1_pre_topc @ 
% 0.91/1.13          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 0.91/1.13         sk_A))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['63', '64'])).
% 0.91/1.13  thf('66', plain,
% 0.91/1.13      ((((v2_compts_1 @ sk_B @ sk_A)
% 0.91/1.13         | ~ (v2_compts_1 @ sk_B @ 
% 0.91/1.13              (k1_pre_topc @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.91/1.13               sk_B))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['60', '65'])).
% 0.91/1.13  thf('67', plain,
% 0.91/1.13      (((v2_compts_1 @ sk_B @ sk_A))
% 0.91/1.13         <= (((v2_compts_1 @ sk_B @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.91/1.13             ((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['35', '66'])).
% 0.91/1.13  thf('68', plain,
% 0.91/1.13      ((~ (v2_compts_1 @ sk_B @ sk_A)) <= (~ ((v2_compts_1 @ sk_B @ sk_A)))),
% 0.91/1.13      inference('split', [status(esa)], ['2'])).
% 0.91/1.13  thf('69', plain,
% 0.91/1.13      (((v2_compts_1 @ sk_B @ sk_A)) | 
% 0.91/1.13       ~
% 0.91/1.13       ((v2_compts_1 @ sk_B @ 
% 0.91/1.13         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.91/1.13       ~
% 0.91/1.13       ((m1_subset_1 @ sk_B @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (u1_struct_0 @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['67', '68'])).
% 0.91/1.13  thf('70', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['50', '51'])).
% 0.91/1.13  thf('71', plain,
% 0.91/1.13      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.91/1.13         <= (~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.91/1.13      inference('split', [status(esa)], ['2'])).
% 0.91/1.13  thf('72', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.91/1.13       ~
% 0.91/1.13       ((m1_subset_1 @ sk_B @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (u1_struct_0 @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['70', '71'])).
% 0.91/1.13  thf('73', plain,
% 0.91/1.13      ((((u1_struct_0 @ 
% 0.91/1.13          (k1_pre_topc @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.91/1.13          = (sk_B)))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['29', '30'])).
% 0.91/1.13  thf('74', plain,
% 0.91/1.13      (((v2_compts_1 @ sk_B @ sk_A)) <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 0.91/1.13      inference('split', [status(esa)], ['0'])).
% 0.91/1.13  thf('75', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['50', '51'])).
% 0.91/1.13  thf('76', plain,
% 0.91/1.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X17)
% 0.91/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.91/1.13          | (v2_compts_1 @ X18 @ X16)
% 0.91/1.13          | ~ (v2_compts_1 @ X18 @ X17)
% 0.91/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.91/1.13          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.91/1.13      inference('simplify', [status(thm)], ['17'])).
% 0.91/1.13  thf('77', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (~ (m1_pre_topc @ X0 @ sk_A)
% 0.91/1.13           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.13           | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.91/1.13           | (v2_compts_1 @ sk_B @ X0)
% 0.91/1.13           | ~ (l1_pre_topc @ sk_A)))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['75', '76'])).
% 0.91/1.13  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('79', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (~ (m1_pre_topc @ X0 @ sk_A)
% 0.91/1.13           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.13           | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.91/1.13           | (v2_compts_1 @ sk_B @ X0)))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['77', '78'])).
% 0.91/1.13  thf('80', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          ((v2_compts_1 @ sk_B @ X0)
% 0.91/1.13           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.13           | ~ (m1_pre_topc @ X0 @ sk_A)))
% 0.91/1.13         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.91/1.13             ((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['74', '79'])).
% 0.91/1.13  thf('81', plain,
% 0.91/1.13      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))
% 0.91/1.13         | ~ (m1_pre_topc @ 
% 0.91/1.13              (k1_pre_topc @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.91/1.13               sk_B) @ 
% 0.91/1.13              sk_A)
% 0.91/1.13         | (v2_compts_1 @ sk_B @ 
% 0.91/1.13            (k1_pre_topc @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))))
% 0.91/1.13         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.91/1.13             ((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['73', '80'])).
% 0.91/1.13  thf('82', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.91/1.13      inference('demod', [status(thm)], ['32', '33'])).
% 0.91/1.13  thf('83', plain,
% 0.91/1.13      (((~ (m1_pre_topc @ 
% 0.91/1.13            (k1_pre_topc @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 0.91/1.13            sk_A)
% 0.91/1.13         | (v2_compts_1 @ sk_B @ 
% 0.91/1.13            (k1_pre_topc @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))))
% 0.91/1.13         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.91/1.13             ((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['81', '82'])).
% 0.91/1.13  thf('84', plain,
% 0.91/1.13      (((m1_pre_topc @ 
% 0.91/1.13         (k1_pre_topc @ 
% 0.91/1.13          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 0.91/1.13         sk_A))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['63', '64'])).
% 0.91/1.13  thf('85', plain,
% 0.91/1.13      (((v2_compts_1 @ sk_B @ 
% 0.91/1.13         (k1_pre_topc @ 
% 0.91/1.13          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 0.91/1.13         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.91/1.13             ((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['83', '84'])).
% 0.91/1.13  thf('86', plain,
% 0.91/1.13      (((m1_pre_topc @ 
% 0.91/1.13         (k1_pre_topc @ 
% 0.91/1.13          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 0.91/1.13         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['11', '12'])).
% 0.91/1.13  thf('87', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X0)
% 0.91/1.13          | (l1_pre_topc @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.13  thf('88', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_B @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (u1_struct_0 @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('split', [status(esa)], ['7'])).
% 0.91/1.13  thf('89', plain,
% 0.91/1.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X17)
% 0.91/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.91/1.13          | (v2_compts_1 @ X18 @ X17)
% 0.91/1.13          | ~ (v2_compts_1 @ X18 @ X16)
% 0.91/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.91/1.13          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.91/1.13      inference('simplify', [status(thm)], ['53'])).
% 0.91/1.13  thf('90', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (~ (m1_pre_topc @ X0 @ 
% 0.91/1.13              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.91/1.13           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.13           | ~ (v2_compts_1 @ sk_B @ X0)
% 0.91/1.13           | (v2_compts_1 @ sk_B @ 
% 0.91/1.13              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.91/1.13           | ~ (l1_pre_topc @ 
% 0.91/1.13                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['88', '89'])).
% 0.91/1.13  thf('91', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (~ (l1_pre_topc @ sk_A)
% 0.91/1.13           | (v2_compts_1 @ sk_B @ 
% 0.91/1.13              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.91/1.13           | ~ (v2_compts_1 @ sk_B @ X0)
% 0.91/1.13           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.13           | ~ (m1_pre_topc @ X0 @ 
% 0.91/1.13                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['87', '90'])).
% 0.91/1.13  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('93', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          ((v2_compts_1 @ sk_B @ 
% 0.91/1.13            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.91/1.13           | ~ (v2_compts_1 @ sk_B @ X0)
% 0.91/1.13           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.13           | ~ (m1_pre_topc @ X0 @ 
% 0.91/1.13                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['91', '92'])).
% 0.91/1.13  thf('94', plain,
% 0.91/1.13      (((~ (m1_subset_1 @ sk_B @ 
% 0.91/1.13            (k1_zfmisc_1 @ 
% 0.91/1.13             (u1_struct_0 @ 
% 0.91/1.13              (k1_pre_topc @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.91/1.13               sk_B))))
% 0.91/1.13         | ~ (v2_compts_1 @ sk_B @ 
% 0.91/1.13              (k1_pre_topc @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.91/1.13               sk_B))
% 0.91/1.13         | (v2_compts_1 @ sk_B @ 
% 0.91/1.13            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['86', '93'])).
% 0.91/1.13  thf('95', plain,
% 0.91/1.13      ((((u1_struct_0 @ 
% 0.91/1.13          (k1_pre_topc @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.91/1.13          = (sk_B)))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['29', '30'])).
% 0.91/1.13  thf('96', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.91/1.13      inference('demod', [status(thm)], ['32', '33'])).
% 0.91/1.13  thf('97', plain,
% 0.91/1.13      (((~ (v2_compts_1 @ sk_B @ 
% 0.91/1.13            (k1_pre_topc @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.91/1.13         | (v2_compts_1 @ sk_B @ 
% 0.91/1.13            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.91/1.13  thf('98', plain,
% 0.91/1.13      (((v2_compts_1 @ sk_B @ 
% 0.91/1.13         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.91/1.13         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.91/1.13             ((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['85', '97'])).
% 0.91/1.13  thf('99', plain,
% 0.91/1.13      ((~ (v2_compts_1 @ sk_B @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.91/1.13         <= (~
% 0.91/1.13             ((v2_compts_1 @ sk_B @ 
% 0.91/1.13               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.91/1.13      inference('split', [status(esa)], ['2'])).
% 0.91/1.13  thf('100', plain,
% 0.91/1.13      (~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 0.91/1.13       ((v2_compts_1 @ sk_B @ 
% 0.91/1.13         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.91/1.13       ~
% 0.91/1.13       ((m1_subset_1 @ sk_B @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (u1_struct_0 @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['98', '99'])).
% 0.91/1.13  thf('101', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_B @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (u1_struct_0 @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.91/1.13        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('102', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.91/1.13       ((m1_subset_1 @ sk_B @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (u1_struct_0 @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.91/1.13      inference('split', [status(esa)], ['101'])).
% 0.91/1.13  thf('103', plain,
% 0.91/1.13      (((v2_compts_1 @ sk_B @ 
% 0.91/1.13         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.91/1.13        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('104', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.91/1.13      inference('split', [status(esa)], ['103'])).
% 0.91/1.13  thf('105', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (((u1_struct_0 @ 
% 0.91/1.13            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.91/1.13            = (u1_struct_0 @ X0))
% 0.91/1.13          | ~ (l1_pre_topc @ X0))),
% 0.91/1.13      inference('clc', [status(thm)], ['46', '47'])).
% 0.91/1.13  thf('106', plain,
% 0.91/1.13      ((~ (m1_subset_1 @ sk_B @ 
% 0.91/1.13           (k1_zfmisc_1 @ 
% 0.91/1.13            (u1_struct_0 @ 
% 0.91/1.13             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.91/1.13         <= (~
% 0.91/1.13             ((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('split', [status(esa)], ['2'])).
% 0.91/1.13  thf('107', plain,
% 0.91/1.13      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13         | ~ (l1_pre_topc @ sk_A)))
% 0.91/1.13         <= (~
% 0.91/1.13             ((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['105', '106'])).
% 0.91/1.13  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('109', plain,
% 0.91/1.13      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.91/1.13         <= (~
% 0.91/1.13             ((m1_subset_1 @ sk_B @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (u1_struct_0 @ 
% 0.91/1.13                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['107', '108'])).
% 0.91/1.13  thf('110', plain,
% 0.91/1.13      (~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.91/1.13       ((m1_subset_1 @ sk_B @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (u1_struct_0 @ 
% 0.91/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['104', '109'])).
% 0.91/1.13  thf('111', plain, ($false),
% 0.91/1.13      inference('sat_resolution*', [status(thm)],
% 0.91/1.13                ['1', '3', '69', '72', '100', '102', '110'])).
% 0.91/1.13  
% 0.91/1.13  % SZS output end Refutation
% 0.91/1.13  
% 0.91/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
