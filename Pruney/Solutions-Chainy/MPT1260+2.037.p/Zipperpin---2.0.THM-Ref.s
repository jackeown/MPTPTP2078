%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uCglR1U2SL

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:28 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 530 expanded)
%              Number of leaves         :   34 ( 177 expanded)
%              Depth                    :   18
%              Number of atoms          : 1418 (5923 expanded)
%              Number of equality atoms :  106 ( 480 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k1_tops_1 @ X39 @ X38 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X39 ) @ X38 @ ( k2_tops_1 @ X39 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf('8',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v3_pre_topc @ X35 @ X34 )
      | ( ( k1_tops_1 @ X34 @ X35 )
        = X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('15',plain,
    ( ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
        | ~ ( v3_pre_topc @ X35 @ X34 )
        | ( ( k1_tops_1 @ X34 @ X35 )
          = X35 ) )
   <= ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
        | ~ ( v3_pre_topc @ X35 @ X34 )
        | ( ( k1_tops_1 @ X34 @ X35 )
          = X35 ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 ) )
   <= ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(split,[status(esa)],['14'])).

thf('18',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ~ ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
        | ~ ( v3_pre_topc @ X35 @ X34 )
        | ( ( k1_tops_1 @ X34 @ X35 )
          = X35 ) )
    | ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(split,[status(esa)],['14'])).

thf('23',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v3_pre_topc @ X35 @ X34 )
      | ( ( k1_tops_1 @ X34 @ X35 )
        = X35 ) ) ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v3_pre_topc @ X35 @ X34 )
      | ( ( k1_tops_1 @ X34 @ X35 )
        = X35 ) ) ),
    inference(simpl_trail,[status(thm)],['15','23'])).

thf('25',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k2_tops_1 @ X33 @ X32 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X33 ) @ ( k2_pre_topc @ X33 @ X32 ) @ ( k1_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('39',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['11','37','38'])).

thf('40',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['9','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['40','47'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('54',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('56',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('59',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('62',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('63',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('64',plain,(
    ! [X6: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','65'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('67',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('68',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('69',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('70',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) ) )
      = ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) ) @ X16 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X1 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['66','72'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_tarski @ X18 @ X17 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('76',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('77',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X6: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('80',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['73','78','83'])).

thf('85',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['48','84'])).

thf('86',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['7','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['73','78','83'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('89',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X20 @ X19 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k1_tops_1 @ X37 @ X36 )
       != X36 )
      | ( v3_pre_topc @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('92',plain,
    ( ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 )
        | ( ( k1_tops_1 @ X37 @ X36 )
         != X36 )
        | ( v3_pre_topc @ X36 @ X37 ) )
   <= ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 )
        | ( ( k1_tops_1 @ X37 @ X36 )
         != X36 )
        | ( v3_pre_topc @ X36 @ X37 ) ) ),
    inference(split,[status(esa)],['91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) )
   <= ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(split,[status(esa)],['91'])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ~ ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 )
        | ( ( k1_tops_1 @ X37 @ X36 )
         != X36 )
        | ( v3_pre_topc @ X36 @ X37 ) )
    | ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(split,[status(esa)],['91'])).

thf('99',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( ( k1_tops_1 @ X37 @ X36 )
       != X36 )
      | ( v3_pre_topc @ X36 @ X37 ) ) ),
    inference('sat_resolution*',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( ( k1_tops_1 @ X37 @ X36 )
       != X36 )
      | ( v3_pre_topc @ X36 @ X37 ) ) ),
    inference(simpl_trail,[status(thm)],['92','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
       != ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
      | ( v3_pre_topc @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['73','78','83'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['73','78','83'])).

thf('112',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('114',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['11','37'])).

thf('115',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['113','114'])).

thf('116',plain,(
    ( k1_tops_1 @ sk_A @ sk_B )
 != sk_B ),
    inference(clc,[status(thm)],['112','115'])).

thf('117',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['86','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uCglR1U2SL
% 0.14/0.38  % Computer   : n004.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 13:43:54 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 1.06/1.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.32  % Solved by: fo/fo7.sh
% 1.06/1.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.32  % done 1179 iterations in 0.830s
% 1.06/1.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.32  % SZS output start Refutation
% 1.06/1.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.32  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.32  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.06/1.32  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.06/1.32  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.06/1.32  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.06/1.32  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.32  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.06/1.32  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.06/1.32  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.32  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.06/1.32  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.06/1.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.32  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.06/1.32  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.32  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.32  thf(t76_tops_1, conjecture,
% 1.06/1.32    (![A:$i]:
% 1.06/1.32     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.32       ( ![B:$i]:
% 1.06/1.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.32           ( ( v3_pre_topc @ B @ A ) <=>
% 1.06/1.32             ( ( k2_tops_1 @ A @ B ) =
% 1.06/1.32               ( k7_subset_1 @
% 1.06/1.32                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 1.06/1.32  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.32    (~( ![A:$i]:
% 1.06/1.32        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.32          ( ![B:$i]:
% 1.06/1.32            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.32              ( ( v3_pre_topc @ B @ A ) <=>
% 1.06/1.32                ( ( k2_tops_1 @ A @ B ) =
% 1.06/1.32                  ( k7_subset_1 @
% 1.06/1.32                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 1.06/1.32    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 1.06/1.32  thf('0', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf(t74_tops_1, axiom,
% 1.06/1.32    (![A:$i]:
% 1.06/1.32     ( ( l1_pre_topc @ A ) =>
% 1.06/1.32       ( ![B:$i]:
% 1.06/1.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.32           ( ( k1_tops_1 @ A @ B ) =
% 1.06/1.32             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.06/1.32  thf('1', plain,
% 1.06/1.32      (![X38 : $i, X39 : $i]:
% 1.06/1.32         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.06/1.32          | ((k1_tops_1 @ X39 @ X38)
% 1.06/1.32              = (k7_subset_1 @ (u1_struct_0 @ X39) @ X38 @ 
% 1.06/1.32                 (k2_tops_1 @ X39 @ X38)))
% 1.06/1.32          | ~ (l1_pre_topc @ X39))),
% 1.06/1.32      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.06/1.32  thf('2', plain,
% 1.06/1.32      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.32        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.32            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.06/1.32      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.32  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('4', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf(redefinition_k7_subset_1, axiom,
% 1.06/1.32    (![A:$i,B:$i,C:$i]:
% 1.06/1.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.32       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.06/1.32  thf('5', plain,
% 1.06/1.32      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.06/1.32         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 1.06/1.32          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 1.06/1.32      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.06/1.32  thf('6', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.32           = (k4_xboole_0 @ sk_B @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['4', '5'])).
% 1.06/1.32  thf('7', plain,
% 1.06/1.32      (((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.32         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.32      inference('demod', [status(thm)], ['2', '3', '6'])).
% 1.06/1.32  thf('8', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.06/1.32        | (v3_pre_topc @ sk_B @ sk_A))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('9', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.06/1.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.06/1.32      inference('split', [status(esa)], ['8'])).
% 1.06/1.32  thf('10', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.06/1.32        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('11', plain,
% 1.06/1.32      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 1.06/1.32       ~
% 1.06/1.32       (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 1.06/1.32      inference('split', [status(esa)], ['10'])).
% 1.06/1.32  thf('12', plain,
% 1.06/1.32      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.32      inference('split', [status(esa)], ['8'])).
% 1.06/1.32  thf('13', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf(t55_tops_1, axiom,
% 1.06/1.32    (![A:$i]:
% 1.06/1.32     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.32       ( ![B:$i]:
% 1.06/1.32         ( ( l1_pre_topc @ B ) =>
% 1.06/1.32           ( ![C:$i]:
% 1.06/1.32             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.32               ( ![D:$i]:
% 1.06/1.32                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.06/1.32                   ( ( ( v3_pre_topc @ D @ B ) =>
% 1.06/1.32                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 1.06/1.32                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 1.06/1.32                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.32  thf('14', plain,
% 1.06/1.32      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.06/1.32         (~ (l1_pre_topc @ X34)
% 1.06/1.32          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.06/1.32          | ~ (v3_pre_topc @ X35 @ X34)
% 1.06/1.32          | ((k1_tops_1 @ X34 @ X35) = (X35))
% 1.06/1.32          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.06/1.32          | ~ (l1_pre_topc @ X37)
% 1.06/1.32          | ~ (v2_pre_topc @ X37))),
% 1.06/1.32      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.06/1.32  thf('15', plain,
% 1.06/1.32      ((![X34 : $i, X35 : $i]:
% 1.06/1.32          (~ (l1_pre_topc @ X34)
% 1.06/1.32           | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.06/1.32           | ~ (v3_pre_topc @ X35 @ X34)
% 1.06/1.32           | ((k1_tops_1 @ X34 @ X35) = (X35))))
% 1.06/1.32         <= ((![X34 : $i, X35 : $i]:
% 1.06/1.32                (~ (l1_pre_topc @ X34)
% 1.06/1.32                 | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.06/1.32                 | ~ (v3_pre_topc @ X35 @ X34)
% 1.06/1.32                 | ((k1_tops_1 @ X34 @ X35) = (X35)))))),
% 1.06/1.32      inference('split', [status(esa)], ['14'])).
% 1.06/1.32  thf('16', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('17', plain,
% 1.06/1.32      ((![X36 : $i, X37 : $i]:
% 1.06/1.32          (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.06/1.32           | ~ (l1_pre_topc @ X37)
% 1.06/1.32           | ~ (v2_pre_topc @ X37)))
% 1.06/1.32         <= ((![X36 : $i, X37 : $i]:
% 1.06/1.32                (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.06/1.32                 | ~ (l1_pre_topc @ X37)
% 1.06/1.32                 | ~ (v2_pre_topc @ X37))))),
% 1.06/1.32      inference('split', [status(esa)], ['14'])).
% 1.06/1.32  thf('18', plain,
% 1.06/1.32      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 1.06/1.32         <= ((![X36 : $i, X37 : $i]:
% 1.06/1.32                (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.06/1.32                 | ~ (l1_pre_topc @ X37)
% 1.06/1.32                 | ~ (v2_pre_topc @ X37))))),
% 1.06/1.32      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.32  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('21', plain,
% 1.06/1.32      (~
% 1.06/1.32       (![X36 : $i, X37 : $i]:
% 1.06/1.32          (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.06/1.32           | ~ (l1_pre_topc @ X37)
% 1.06/1.32           | ~ (v2_pre_topc @ X37)))),
% 1.06/1.32      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.06/1.32  thf('22', plain,
% 1.06/1.32      ((![X34 : $i, X35 : $i]:
% 1.06/1.32          (~ (l1_pre_topc @ X34)
% 1.06/1.32           | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.06/1.32           | ~ (v3_pre_topc @ X35 @ X34)
% 1.06/1.32           | ((k1_tops_1 @ X34 @ X35) = (X35)))) | 
% 1.06/1.32       (![X36 : $i, X37 : $i]:
% 1.06/1.32          (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.06/1.32           | ~ (l1_pre_topc @ X37)
% 1.06/1.32           | ~ (v2_pre_topc @ X37)))),
% 1.06/1.32      inference('split', [status(esa)], ['14'])).
% 1.06/1.32  thf('23', plain,
% 1.06/1.32      ((![X34 : $i, X35 : $i]:
% 1.06/1.32          (~ (l1_pre_topc @ X34)
% 1.06/1.32           | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.06/1.32           | ~ (v3_pre_topc @ X35 @ X34)
% 1.06/1.32           | ((k1_tops_1 @ X34 @ X35) = (X35))))),
% 1.06/1.32      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 1.06/1.32  thf('24', plain,
% 1.06/1.32      (![X34 : $i, X35 : $i]:
% 1.06/1.32         (~ (l1_pre_topc @ X34)
% 1.06/1.32          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.06/1.32          | ~ (v3_pre_topc @ X35 @ X34)
% 1.06/1.32          | ((k1_tops_1 @ X34 @ X35) = (X35)))),
% 1.06/1.32      inference('simpl_trail', [status(thm)], ['15', '23'])).
% 1.06/1.32  thf('25', plain,
% 1.06/1.32      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 1.06/1.32        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 1.06/1.32        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.32      inference('sup-', [status(thm)], ['13', '24'])).
% 1.06/1.32  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('27', plain,
% 1.06/1.32      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.06/1.32      inference('demod', [status(thm)], ['25', '26'])).
% 1.06/1.32  thf('28', plain,
% 1.06/1.32      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.06/1.32         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.32      inference('sup-', [status(thm)], ['12', '27'])).
% 1.06/1.32  thf('29', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf(l78_tops_1, axiom,
% 1.06/1.32    (![A:$i]:
% 1.06/1.32     ( ( l1_pre_topc @ A ) =>
% 1.06/1.32       ( ![B:$i]:
% 1.06/1.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.32           ( ( k2_tops_1 @ A @ B ) =
% 1.06/1.32             ( k7_subset_1 @
% 1.06/1.32               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.06/1.32               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.06/1.32  thf('30', plain,
% 1.06/1.32      (![X32 : $i, X33 : $i]:
% 1.06/1.32         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.06/1.32          | ((k2_tops_1 @ X33 @ X32)
% 1.06/1.32              = (k7_subset_1 @ (u1_struct_0 @ X33) @ 
% 1.06/1.32                 (k2_pre_topc @ X33 @ X32) @ (k1_tops_1 @ X33 @ X32)))
% 1.06/1.32          | ~ (l1_pre_topc @ X33))),
% 1.06/1.32      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.06/1.32  thf('31', plain,
% 1.06/1.32      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.32        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.06/1.32      inference('sup-', [status(thm)], ['29', '30'])).
% 1.06/1.32  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('33', plain,
% 1.06/1.32      (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.06/1.32            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.32      inference('demod', [status(thm)], ['31', '32'])).
% 1.06/1.32  thf('34', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.06/1.32         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.32      inference('sup+', [status(thm)], ['28', '33'])).
% 1.06/1.32  thf('35', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.06/1.32         <= (~
% 1.06/1.32             (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.06/1.32      inference('split', [status(esa)], ['10'])).
% 1.06/1.32  thf('36', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.32         <= (~
% 1.06/1.32             (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 1.06/1.32             ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.32      inference('sup-', [status(thm)], ['34', '35'])).
% 1.06/1.32  thf('37', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.06/1.32       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.06/1.32      inference('simplify', [status(thm)], ['36'])).
% 1.06/1.32  thf('38', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.06/1.32       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.06/1.32      inference('split', [status(esa)], ['8'])).
% 1.06/1.32  thf('39', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 1.06/1.32      inference('sat_resolution*', [status(thm)], ['11', '37', '38'])).
% 1.06/1.32  thf('40', plain,
% 1.06/1.32      (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.06/1.32            sk_B))),
% 1.06/1.32      inference('simpl_trail', [status(thm)], ['9', '39'])).
% 1.06/1.32  thf('41', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf(dt_k2_pre_topc, axiom,
% 1.06/1.32    (![A:$i,B:$i]:
% 1.06/1.32     ( ( ( l1_pre_topc @ A ) & 
% 1.06/1.32         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.32       ( m1_subset_1 @
% 1.06/1.32         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.06/1.32  thf('42', plain,
% 1.06/1.32      (![X30 : $i, X31 : $i]:
% 1.06/1.32         (~ (l1_pre_topc @ X30)
% 1.06/1.32          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.06/1.32          | (m1_subset_1 @ (k2_pre_topc @ X30 @ X31) @ 
% 1.06/1.32             (k1_zfmisc_1 @ (u1_struct_0 @ X30))))),
% 1.06/1.32      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.06/1.32  thf('43', plain,
% 1.06/1.32      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.06/1.32         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.32        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.32      inference('sup-', [status(thm)], ['41', '42'])).
% 1.06/1.32  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('45', plain,
% 1.06/1.32      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.06/1.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('demod', [status(thm)], ['43', '44'])).
% 1.06/1.32  thf('46', plain,
% 1.06/1.32      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.06/1.32         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 1.06/1.32          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 1.06/1.32      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.06/1.32  thf('47', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.06/1.32           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['45', '46'])).
% 1.06/1.32  thf('48', plain,
% 1.06/1.32      (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 1.06/1.32      inference('demod', [status(thm)], ['40', '47'])).
% 1.06/1.32  thf(idempotence_k3_xboole_0, axiom,
% 1.06/1.32    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.06/1.32  thf('49', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.06/1.32      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.06/1.32  thf(t12_setfam_1, axiom,
% 1.06/1.32    (![A:$i,B:$i]:
% 1.06/1.32     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.06/1.32  thf('50', plain,
% 1.06/1.32      (![X25 : $i, X26 : $i]:
% 1.06/1.32         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 1.06/1.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.06/1.32  thf('51', plain,
% 1.06/1.32      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.06/1.32      inference('demod', [status(thm)], ['49', '50'])).
% 1.06/1.32  thf(t100_xboole_1, axiom,
% 1.06/1.32    (![A:$i,B:$i]:
% 1.06/1.32     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.06/1.32  thf('52', plain,
% 1.06/1.32      (![X1 : $i, X2 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X1 @ X2)
% 1.06/1.32           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.06/1.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.06/1.32  thf('53', plain,
% 1.06/1.32      (![X25 : $i, X26 : $i]:
% 1.06/1.32         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 1.06/1.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.06/1.32  thf('54', plain,
% 1.06/1.32      (![X1 : $i, X2 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X1 @ X2)
% 1.06/1.32           = (k5_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))))),
% 1.06/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.06/1.32  thf('55', plain,
% 1.06/1.32      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.06/1.32      inference('sup+', [status(thm)], ['51', '54'])).
% 1.06/1.32  thf(t3_boole, axiom,
% 1.06/1.32    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.06/1.32  thf('56', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.06/1.32      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.32  thf(t48_xboole_1, axiom,
% 1.06/1.32    (![A:$i,B:$i]:
% 1.06/1.32     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.06/1.32  thf('57', plain,
% 1.06/1.32      (![X12 : $i, X13 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 1.06/1.32           = (k3_xboole_0 @ X12 @ X13))),
% 1.06/1.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.06/1.32  thf('58', plain,
% 1.06/1.32      (![X25 : $i, X26 : $i]:
% 1.06/1.32         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 1.06/1.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.06/1.32  thf('59', plain,
% 1.06/1.32      (![X12 : $i, X13 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 1.06/1.32           = (k1_setfam_1 @ (k2_tarski @ X12 @ X13)))),
% 1.06/1.32      inference('demod', [status(thm)], ['57', '58'])).
% 1.06/1.32  thf('60', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X0 @ X0)
% 1.06/1.32           = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 1.06/1.32      inference('sup+', [status(thm)], ['56', '59'])).
% 1.06/1.32  thf('61', plain,
% 1.06/1.32      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.06/1.32      inference('sup+', [status(thm)], ['51', '54'])).
% 1.06/1.32  thf(t2_boole, axiom,
% 1.06/1.32    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.06/1.32  thf('62', plain,
% 1.06/1.32      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.32      inference('cnf', [status(esa)], [t2_boole])).
% 1.06/1.32  thf('63', plain,
% 1.06/1.32      (![X25 : $i, X26 : $i]:
% 1.06/1.32         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 1.06/1.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.06/1.32  thf('64', plain,
% 1.06/1.32      (![X6 : $i]:
% 1.06/1.32         ((k1_setfam_1 @ (k2_tarski @ X6 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.06/1.32      inference('demod', [status(thm)], ['62', '63'])).
% 1.06/1.32  thf('65', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.06/1.32      inference('demod', [status(thm)], ['60', '61', '64'])).
% 1.06/1.32  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.06/1.32      inference('demod', [status(thm)], ['55', '65'])).
% 1.06/1.32  thf(t49_xboole_1, axiom,
% 1.06/1.32    (![A:$i,B:$i,C:$i]:
% 1.06/1.32     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.06/1.32       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.06/1.32  thf('67', plain,
% 1.06/1.32      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.06/1.32         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 1.06/1.32           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 1.06/1.32      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.06/1.32  thf('68', plain,
% 1.06/1.32      (![X25 : $i, X26 : $i]:
% 1.06/1.32         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 1.06/1.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.06/1.32  thf('69', plain,
% 1.06/1.32      (![X25 : $i, X26 : $i]:
% 1.06/1.32         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 1.06/1.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.06/1.32  thf('70', plain,
% 1.06/1.32      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.06/1.32         ((k1_setfam_1 @ (k2_tarski @ X14 @ (k4_xboole_0 @ X15 @ X16)))
% 1.06/1.32           = (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X14 @ X15)) @ X16))),
% 1.06/1.32      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.06/1.32  thf('71', plain,
% 1.06/1.32      (![X1 : $i, X2 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X1 @ X2)
% 1.06/1.32           = (k5_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))))),
% 1.06/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.06/1.32  thf('72', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 1.06/1.32           = (k5_xboole_0 @ X2 @ 
% 1.06/1.32              (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X1)) @ X0)))),
% 1.06/1.32      inference('sup+', [status(thm)], ['70', '71'])).
% 1.06/1.32  thf('73', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X1 @ 
% 1.06/1.32           (k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 1.06/1.32           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.06/1.32      inference('sup+', [status(thm)], ['66', '72'])).
% 1.06/1.32  thf(commutativity_k2_tarski, axiom,
% 1.06/1.32    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.06/1.32  thf('74', plain,
% 1.06/1.32      (![X17 : $i, X18 : $i]:
% 1.06/1.32         ((k2_tarski @ X18 @ X17) = (k2_tarski @ X17 @ X18))),
% 1.06/1.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.06/1.32  thf(t47_xboole_1, axiom,
% 1.06/1.32    (![A:$i,B:$i]:
% 1.06/1.32     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.06/1.32  thf('75', plain,
% 1.06/1.32      (![X10 : $i, X11 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 1.06/1.32           = (k4_xboole_0 @ X10 @ X11))),
% 1.06/1.32      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.06/1.32  thf('76', plain,
% 1.06/1.32      (![X25 : $i, X26 : $i]:
% 1.06/1.32         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 1.06/1.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.06/1.32  thf('77', plain,
% 1.06/1.32      (![X10 : $i, X11 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X10 @ (k1_setfam_1 @ (k2_tarski @ X10 @ X11)))
% 1.06/1.32           = (k4_xboole_0 @ X10 @ X11))),
% 1.06/1.32      inference('demod', [status(thm)], ['75', '76'])).
% 1.06/1.32  thf('78', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.06/1.32           = (k4_xboole_0 @ X0 @ X1))),
% 1.06/1.32      inference('sup+', [status(thm)], ['74', '77'])).
% 1.06/1.32  thf('79', plain,
% 1.06/1.32      (![X6 : $i]:
% 1.06/1.32         ((k1_setfam_1 @ (k2_tarski @ X6 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.06/1.32      inference('demod', [status(thm)], ['62', '63'])).
% 1.06/1.32  thf('80', plain,
% 1.06/1.32      (![X1 : $i, X2 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X1 @ X2)
% 1.06/1.32           = (k5_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))))),
% 1.06/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.06/1.32  thf('81', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.06/1.32      inference('sup+', [status(thm)], ['79', '80'])).
% 1.06/1.32  thf('82', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.06/1.32      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.32  thf('83', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.06/1.32      inference('sup+', [status(thm)], ['81', '82'])).
% 1.06/1.32  thf('84', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (X1))),
% 1.06/1.32      inference('demod', [status(thm)], ['73', '78', '83'])).
% 1.06/1.32  thf('85', plain,
% 1.06/1.32      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 1.06/1.32      inference('sup+', [status(thm)], ['48', '84'])).
% 1.06/1.32  thf('86', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 1.06/1.32      inference('sup+', [status(thm)], ['7', '85'])).
% 1.06/1.32  thf('87', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (X1))),
% 1.06/1.32      inference('demod', [status(thm)], ['73', '78', '83'])).
% 1.06/1.32  thf('88', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf(dt_k7_subset_1, axiom,
% 1.06/1.32    (![A:$i,B:$i,C:$i]:
% 1.06/1.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.32       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.06/1.32  thf('89', plain,
% 1.06/1.32      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.06/1.32         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 1.06/1.32          | (m1_subset_1 @ (k7_subset_1 @ X20 @ X19 @ X21) @ 
% 1.06/1.32             (k1_zfmisc_1 @ X20)))),
% 1.06/1.32      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 1.06/1.32  thf('90', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.06/1.32          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('sup-', [status(thm)], ['88', '89'])).
% 1.06/1.32  thf('91', plain,
% 1.06/1.32      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.06/1.32         (~ (l1_pre_topc @ X34)
% 1.06/1.32          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.06/1.32          | ((k1_tops_1 @ X37 @ X36) != (X36))
% 1.06/1.32          | (v3_pre_topc @ X36 @ X37)
% 1.06/1.32          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.06/1.32          | ~ (l1_pre_topc @ X37)
% 1.06/1.32          | ~ (v2_pre_topc @ X37))),
% 1.06/1.32      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.06/1.32  thf('92', plain,
% 1.06/1.32      ((![X36 : $i, X37 : $i]:
% 1.06/1.32          (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.06/1.32           | ~ (l1_pre_topc @ X37)
% 1.06/1.32           | ~ (v2_pre_topc @ X37)
% 1.06/1.32           | ((k1_tops_1 @ X37 @ X36) != (X36))
% 1.06/1.32           | (v3_pre_topc @ X36 @ X37)))
% 1.06/1.32         <= ((![X36 : $i, X37 : $i]:
% 1.06/1.32                (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.06/1.32                 | ~ (l1_pre_topc @ X37)
% 1.06/1.32                 | ~ (v2_pre_topc @ X37)
% 1.06/1.32                 | ((k1_tops_1 @ X37 @ X36) != (X36))
% 1.06/1.32                 | (v3_pre_topc @ X36 @ X37))))),
% 1.06/1.32      inference('split', [status(esa)], ['91'])).
% 1.06/1.32  thf('93', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('94', plain,
% 1.06/1.32      ((![X34 : $i, X35 : $i]:
% 1.06/1.32          (~ (l1_pre_topc @ X34)
% 1.06/1.32           | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))))
% 1.06/1.32         <= ((![X34 : $i, X35 : $i]:
% 1.06/1.32                (~ (l1_pre_topc @ X34)
% 1.06/1.32                 | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34))))))),
% 1.06/1.32      inference('split', [status(esa)], ['91'])).
% 1.06/1.32  thf('95', plain,
% 1.06/1.32      ((~ (l1_pre_topc @ sk_A))
% 1.06/1.32         <= ((![X34 : $i, X35 : $i]:
% 1.06/1.32                (~ (l1_pre_topc @ X34)
% 1.06/1.32                 | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34))))))),
% 1.06/1.32      inference('sup-', [status(thm)], ['93', '94'])).
% 1.06/1.32  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('97', plain,
% 1.06/1.32      (~
% 1.06/1.32       (![X34 : $i, X35 : $i]:
% 1.06/1.32          (~ (l1_pre_topc @ X34)
% 1.06/1.32           | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))))),
% 1.06/1.32      inference('demod', [status(thm)], ['95', '96'])).
% 1.06/1.32  thf('98', plain,
% 1.06/1.32      ((![X36 : $i, X37 : $i]:
% 1.06/1.32          (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.06/1.32           | ~ (l1_pre_topc @ X37)
% 1.06/1.32           | ~ (v2_pre_topc @ X37)
% 1.06/1.32           | ((k1_tops_1 @ X37 @ X36) != (X36))
% 1.06/1.32           | (v3_pre_topc @ X36 @ X37))) | 
% 1.06/1.32       (![X34 : $i, X35 : $i]:
% 1.06/1.32          (~ (l1_pre_topc @ X34)
% 1.06/1.32           | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))))),
% 1.06/1.32      inference('split', [status(esa)], ['91'])).
% 1.06/1.32  thf('99', plain,
% 1.06/1.32      ((![X36 : $i, X37 : $i]:
% 1.06/1.32          (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.06/1.32           | ~ (l1_pre_topc @ X37)
% 1.06/1.32           | ~ (v2_pre_topc @ X37)
% 1.06/1.32           | ((k1_tops_1 @ X37 @ X36) != (X36))
% 1.06/1.32           | (v3_pre_topc @ X36 @ X37)))),
% 1.06/1.32      inference('sat_resolution*', [status(thm)], ['97', '98'])).
% 1.06/1.32  thf('100', plain,
% 1.06/1.32      (![X36 : $i, X37 : $i]:
% 1.06/1.32         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.06/1.32          | ~ (l1_pre_topc @ X37)
% 1.06/1.32          | ~ (v2_pre_topc @ X37)
% 1.06/1.32          | ((k1_tops_1 @ X37 @ X36) != (X36))
% 1.06/1.32          | (v3_pre_topc @ X36 @ X37))),
% 1.06/1.32      inference('simpl_trail', [status(thm)], ['92', '99'])).
% 1.06/1.32  thf('101', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         ((v3_pre_topc @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.06/1.32           sk_A)
% 1.06/1.32          | ((k1_tops_1 @ sk_A @ 
% 1.06/1.32              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 1.06/1.32              != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 1.06/1.32          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.32          | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.32      inference('sup-', [status(thm)], ['90', '100'])).
% 1.06/1.32  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('104', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         ((v3_pre_topc @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.06/1.32           sk_A)
% 1.06/1.32          | ((k1_tops_1 @ sk_A @ 
% 1.06/1.32              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 1.06/1.32              != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)))),
% 1.06/1.32      inference('demod', [status(thm)], ['101', '102', '103'])).
% 1.06/1.32  thf('105', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.32           = (k4_xboole_0 @ sk_B @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['4', '5'])).
% 1.06/1.32  thf('106', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.32           = (k4_xboole_0 @ sk_B @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['4', '5'])).
% 1.06/1.32  thf('107', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.32           = (k4_xboole_0 @ sk_B @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['4', '5'])).
% 1.06/1.32  thf('108', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         ((v3_pre_topc @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 1.06/1.32          | ((k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 1.06/1.32              != (k4_xboole_0 @ sk_B @ X0)))),
% 1.06/1.32      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 1.06/1.32  thf('109', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         (((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.32            != (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_B)))
% 1.06/1.32          | (v3_pre_topc @ (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_B)) @ 
% 1.06/1.32             sk_A))),
% 1.06/1.32      inference('sup-', [status(thm)], ['87', '108'])).
% 1.06/1.32  thf('110', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (X1))),
% 1.06/1.32      inference('demod', [status(thm)], ['73', '78', '83'])).
% 1.06/1.32  thf('111', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (X1))),
% 1.06/1.32      inference('demod', [status(thm)], ['73', '78', '83'])).
% 1.06/1.32  thf('112', plain,
% 1.06/1.32      ((((k1_tops_1 @ sk_A @ sk_B) != (sk_B)) | (v3_pre_topc @ sk_B @ sk_A))),
% 1.06/1.32      inference('demod', [status(thm)], ['109', '110', '111'])).
% 1.06/1.32  thf('113', plain,
% 1.06/1.32      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.32      inference('split', [status(esa)], ['10'])).
% 1.06/1.32  thf('114', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.06/1.32      inference('sat_resolution*', [status(thm)], ['11', '37'])).
% 1.06/1.32  thf('115', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 1.06/1.32      inference('simpl_trail', [status(thm)], ['113', '114'])).
% 1.06/1.32  thf('116', plain, (((k1_tops_1 @ sk_A @ sk_B) != (sk_B))),
% 1.06/1.32      inference('clc', [status(thm)], ['112', '115'])).
% 1.06/1.32  thf('117', plain, ($false),
% 1.06/1.32      inference('simplify_reflect-', [status(thm)], ['86', '116'])).
% 1.06/1.32  
% 1.06/1.32  % SZS output end Refutation
% 1.06/1.32  
% 1.06/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
