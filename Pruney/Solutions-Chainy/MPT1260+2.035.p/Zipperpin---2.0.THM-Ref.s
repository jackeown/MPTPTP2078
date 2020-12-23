%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3XrK6Ll7M3

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:27 EST 2020

% Result     : Theorem 8.95s
% Output     : Refutation 9.07s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 689 expanded)
%              Number of leaves         :   45 ( 229 expanded)
%              Depth                    :   18
%              Number of atoms          : 2039 (7761 expanded)
%              Number of equality atoms :  145 ( 569 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( ( k1_tops_1 @ X58 @ X57 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X58 ) @ X57 @ ( k2_tops_1 @ X58 @ X57 ) ) )
      | ~ ( l1_pre_topc @ X58 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k7_subset_1 @ X38 @ X37 @ X39 )
        = ( k4_xboole_0 @ X37 @ X39 ) ) ) ),
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
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v3_pre_topc @ X50 @ X49 )
      | ( ( k1_tops_1 @ X49 @ X50 )
        = X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( v2_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('15',plain,
    ( ! [X49: $i,X50: $i] :
        ( ~ ( l1_pre_topc @ X49 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
        | ~ ( v3_pre_topc @ X50 @ X49 )
        | ( ( k1_tops_1 @ X49 @ X50 )
          = X50 ) )
   <= ! [X49: $i,X50: $i] :
        ( ~ ( l1_pre_topc @ X49 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
        | ~ ( v3_pre_topc @ X50 @ X49 )
        | ( ( k1_tops_1 @ X49 @ X50 )
          = X50 ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ! [X51: $i,X52: $i] :
        ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
        | ~ ( l1_pre_topc @ X52 )
        | ~ ( v2_pre_topc @ X52 ) )
   <= ! [X51: $i,X52: $i] :
        ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
        | ~ ( l1_pre_topc @ X52 )
        | ~ ( v2_pre_topc @ X52 ) ) ),
    inference(split,[status(esa)],['14'])).

thf('18',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X51: $i,X52: $i] :
        ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
        | ~ ( l1_pre_topc @ X52 )
        | ~ ( v2_pre_topc @ X52 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ~ ! [X51: $i,X52: $i] :
        ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
        | ~ ( l1_pre_topc @ X52 )
        | ~ ( v2_pre_topc @ X52 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ! [X49: $i,X50: $i] :
        ( ~ ( l1_pre_topc @ X49 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
        | ~ ( v3_pre_topc @ X50 @ X49 )
        | ( ( k1_tops_1 @ X49 @ X50 )
          = X50 ) )
    | ! [X51: $i,X52: $i] :
        ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
        | ~ ( l1_pre_topc @ X52 )
        | ~ ( v2_pre_topc @ X52 ) ) ),
    inference(split,[status(esa)],['14'])).

thf('23',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v3_pre_topc @ X50 @ X49 )
      | ( ( k1_tops_1 @ X49 @ X50 )
        = X50 ) ) ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v3_pre_topc @ X50 @ X49 )
      | ( ( k1_tops_1 @ X49 @ X50 )
        = X50 ) ) ),
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
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( ( k2_tops_1 @ X48 @ X47 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X48 ) @ ( k2_pre_topc @ X48 @ X47 ) @ ( k1_tops_1 @ X48 @ X47 ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
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

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( l1_pre_topc @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X45 @ X46 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X33 @ X32 @ X34 ) @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k2_pre_topc @ X56 @ X55 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 @ ( k2_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k7_subset_1 @ X38 @ X37 @ X39 )
        = ( k4_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['40','57'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('62',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X17 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('63',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('64',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('65',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('66',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X17 @ X19 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k5_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('69',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('71',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('72',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('73',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('74',plain,(
    ! [X25: $i] :
      ( ( k4_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('75',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('76',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('81',plain,(
    ! [X22: $i] :
      ( ( k3_xboole_0 @ X22 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('82',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('83',plain,(
    ! [X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X22 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('87',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('88',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('90',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','90'])).

thf('92',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['70','94'])).

thf('96',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X22 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('99',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X25: $i] :
      ( ( k4_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['97','102'])).

thf('104',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['58','103'])).

thf('105',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['7','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('107',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('109',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('110',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('111',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('114',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['112','115'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('117',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('118',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('125',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('127',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','128'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('130',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('131',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('132',plain,(
    ! [X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X17 @ X19 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('136',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['129','139'])).

thf('141',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['116','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('143',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X36 @ ( k3_subset_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('144',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['112','115'])).

thf('146',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('148',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['145','148'])).

thf('150',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['144','149'])).

thf('151',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('153',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k1_tops_1 @ X52 @ X51 )
       != X51 )
      | ( v3_pre_topc @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( v2_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('154',plain,
    ( ! [X51: $i,X52: $i] :
        ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
        | ~ ( l1_pre_topc @ X52 )
        | ~ ( v2_pre_topc @ X52 )
        | ( ( k1_tops_1 @ X52 @ X51 )
         != X51 )
        | ( v3_pre_topc @ X51 @ X52 ) )
   <= ! [X51: $i,X52: $i] :
        ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
        | ~ ( l1_pre_topc @ X52 )
        | ~ ( v2_pre_topc @ X52 )
        | ( ( k1_tops_1 @ X52 @ X51 )
         != X51 )
        | ( v3_pre_topc @ X51 @ X52 ) ) ),
    inference(split,[status(esa)],['153'])).

thf('155',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ! [X49: $i,X50: $i] :
        ( ~ ( l1_pre_topc @ X49 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) )
   <= ! [X49: $i,X50: $i] :
        ( ~ ( l1_pre_topc @ X49 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) ) ),
    inference(split,[status(esa)],['153'])).

thf('157',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X49: $i,X50: $i] :
        ( ~ ( l1_pre_topc @ X49 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ~ ! [X49: $i,X50: $i] :
        ( ~ ( l1_pre_topc @ X49 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ! [X51: $i,X52: $i] :
        ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
        | ~ ( l1_pre_topc @ X52 )
        | ~ ( v2_pre_topc @ X52 )
        | ( ( k1_tops_1 @ X52 @ X51 )
         != X51 )
        | ( v3_pre_topc @ X51 @ X52 ) )
    | ! [X49: $i,X50: $i] :
        ( ~ ( l1_pre_topc @ X49 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) ) ),
    inference(split,[status(esa)],['153'])).

thf('161',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( v2_pre_topc @ X52 )
      | ( ( k1_tops_1 @ X52 @ X51 )
       != X51 )
      | ( v3_pre_topc @ X51 @ X52 ) ) ),
    inference('sat_resolution*',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( v2_pre_topc @ X52 )
      | ( ( k1_tops_1 @ X52 @ X51 )
       != X51 )
      | ( v3_pre_topc @ X51 @ X52 ) ) ),
    inference(simpl_trail,[status(thm)],['154','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
       != ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','162'])).

thf('164',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['151','163'])).

thf('165',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','150'])).

thf('166',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','150'])).

thf('169',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['164','165','166','167','168'])).

thf('170',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('171',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['11','37'])).

thf('172',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['170','171'])).

thf('173',plain,(
    ( k1_tops_1 @ sk_A @ sk_B )
 != sk_B ),
    inference(clc,[status(thm)],['169','172'])).

thf('174',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['105','173'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3XrK6Ll7M3
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.95/9.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.95/9.23  % Solved by: fo/fo7.sh
% 8.95/9.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.95/9.23  % done 6805 iterations in 8.776s
% 8.95/9.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.95/9.23  % SZS output start Refutation
% 8.95/9.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.95/9.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.95/9.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.95/9.23  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.95/9.23  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 8.95/9.23  thf(sk_B_type, type, sk_B: $i).
% 8.95/9.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.95/9.23  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 8.95/9.23  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 8.95/9.23  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 8.95/9.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.95/9.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.95/9.23  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 8.95/9.23  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.95/9.23  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 8.95/9.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.95/9.23  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.95/9.23  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 8.95/9.23  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 8.95/9.23  thf(sk_A_type, type, sk_A: $i).
% 8.95/9.23  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 8.95/9.23  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.95/9.23  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 8.95/9.23  thf(t76_tops_1, conjecture,
% 8.95/9.23    (![A:$i]:
% 8.95/9.23     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.95/9.23       ( ![B:$i]:
% 8.95/9.23         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.95/9.23           ( ( v3_pre_topc @ B @ A ) <=>
% 8.95/9.23             ( ( k2_tops_1 @ A @ B ) =
% 8.95/9.23               ( k7_subset_1 @
% 8.95/9.23                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 8.95/9.23  thf(zf_stmt_0, negated_conjecture,
% 8.95/9.23    (~( ![A:$i]:
% 8.95/9.23        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.95/9.23          ( ![B:$i]:
% 8.95/9.23            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.95/9.23              ( ( v3_pre_topc @ B @ A ) <=>
% 8.95/9.23                ( ( k2_tops_1 @ A @ B ) =
% 8.95/9.23                  ( k7_subset_1 @
% 8.95/9.23                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 8.95/9.23    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 8.95/9.23  thf('0', plain,
% 8.95/9.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.95/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.95/9.23  thf(t74_tops_1, axiom,
% 8.95/9.23    (![A:$i]:
% 8.95/9.23     ( ( l1_pre_topc @ A ) =>
% 8.95/9.23       ( ![B:$i]:
% 8.95/9.23         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.95/9.23           ( ( k1_tops_1 @ A @ B ) =
% 8.95/9.23             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 8.95/9.23  thf('1', plain,
% 8.95/9.23      (![X57 : $i, X58 : $i]:
% 8.95/9.23         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 8.95/9.23          | ((k1_tops_1 @ X58 @ X57)
% 8.95/9.23              = (k7_subset_1 @ (u1_struct_0 @ X58) @ X57 @ 
% 8.95/9.23                 (k2_tops_1 @ X58 @ X57)))
% 8.95/9.23          | ~ (l1_pre_topc @ X58))),
% 8.95/9.23      inference('cnf', [status(esa)], [t74_tops_1])).
% 8.95/9.23  thf('2', plain,
% 8.95/9.23      ((~ (l1_pre_topc @ sk_A)
% 8.95/9.23        | ((k1_tops_1 @ sk_A @ sk_B)
% 8.95/9.23            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.95/9.23               (k2_tops_1 @ sk_A @ sk_B))))),
% 8.95/9.23      inference('sup-', [status(thm)], ['0', '1'])).
% 8.95/9.23  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 8.95/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.95/9.23  thf('4', plain,
% 8.95/9.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.95/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.95/9.23  thf(redefinition_k7_subset_1, axiom,
% 8.95/9.23    (![A:$i,B:$i,C:$i]:
% 8.95/9.23     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.95/9.23       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 8.95/9.23  thf('5', plain,
% 8.95/9.23      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.95/9.23         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 8.95/9.23          | ((k7_subset_1 @ X38 @ X37 @ X39) = (k4_xboole_0 @ X37 @ X39)))),
% 8.95/9.23      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.95/9.23  thf('6', plain,
% 8.95/9.23      (![X0 : $i]:
% 8.95/9.23         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.95/9.23           = (k4_xboole_0 @ sk_B @ X0))),
% 8.95/9.23      inference('sup-', [status(thm)], ['4', '5'])).
% 9.07/9.23  thf('7', plain,
% 9.07/9.23      (((k1_tops_1 @ sk_A @ sk_B)
% 9.07/9.23         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 9.07/9.23      inference('demod', [status(thm)], ['2', '3', '6'])).
% 9.07/9.23  thf('8', plain,
% 9.07/9.23      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.23             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 9.07/9.23        | (v3_pre_topc @ sk_B @ sk_A))),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf('9', plain,
% 9.07/9.23      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.23             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 9.07/9.23         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.23                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 9.07/9.23      inference('split', [status(esa)], ['8'])).
% 9.07/9.23  thf('10', plain,
% 9.07/9.23      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.23              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 9.07/9.23        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf('11', plain,
% 9.07/9.23      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 9.07/9.23       ~
% 9.07/9.23       (((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.23             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 9.07/9.23      inference('split', [status(esa)], ['10'])).
% 9.07/9.23  thf('12', plain,
% 9.07/9.23      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 9.07/9.23      inference('split', [status(esa)], ['8'])).
% 9.07/9.23  thf('13', plain,
% 9.07/9.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf(t55_tops_1, axiom,
% 9.07/9.23    (![A:$i]:
% 9.07/9.23     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 9.07/9.23       ( ![B:$i]:
% 9.07/9.23         ( ( l1_pre_topc @ B ) =>
% 9.07/9.23           ( ![C:$i]:
% 9.07/9.23             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.07/9.23               ( ![D:$i]:
% 9.07/9.23                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 9.07/9.23                   ( ( ( v3_pre_topc @ D @ B ) =>
% 9.07/9.23                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 9.07/9.23                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 9.07/9.23                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 9.07/9.23  thf('14', plain,
% 9.07/9.23      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 9.07/9.23         (~ (l1_pre_topc @ X49)
% 9.07/9.23          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 9.07/9.23          | ~ (v3_pre_topc @ X50 @ X49)
% 9.07/9.23          | ((k1_tops_1 @ X49 @ X50) = (X50))
% 9.07/9.23          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 9.07/9.23          | ~ (l1_pre_topc @ X52)
% 9.07/9.23          | ~ (v2_pre_topc @ X52))),
% 9.07/9.23      inference('cnf', [status(esa)], [t55_tops_1])).
% 9.07/9.23  thf('15', plain,
% 9.07/9.23      ((![X49 : $i, X50 : $i]:
% 9.07/9.23          (~ (l1_pre_topc @ X49)
% 9.07/9.23           | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 9.07/9.23           | ~ (v3_pre_topc @ X50 @ X49)
% 9.07/9.23           | ((k1_tops_1 @ X49 @ X50) = (X50))))
% 9.07/9.23         <= ((![X49 : $i, X50 : $i]:
% 9.07/9.23                (~ (l1_pre_topc @ X49)
% 9.07/9.23                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 9.07/9.23                 | ~ (v3_pre_topc @ X50 @ X49)
% 9.07/9.23                 | ((k1_tops_1 @ X49 @ X50) = (X50)))))),
% 9.07/9.23      inference('split', [status(esa)], ['14'])).
% 9.07/9.23  thf('16', plain,
% 9.07/9.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf('17', plain,
% 9.07/9.23      ((![X51 : $i, X52 : $i]:
% 9.07/9.23          (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 9.07/9.23           | ~ (l1_pre_topc @ X52)
% 9.07/9.23           | ~ (v2_pre_topc @ X52)))
% 9.07/9.23         <= ((![X51 : $i, X52 : $i]:
% 9.07/9.23                (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 9.07/9.23                 | ~ (l1_pre_topc @ X52)
% 9.07/9.23                 | ~ (v2_pre_topc @ X52))))),
% 9.07/9.23      inference('split', [status(esa)], ['14'])).
% 9.07/9.23  thf('18', plain,
% 9.07/9.23      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 9.07/9.23         <= ((![X51 : $i, X52 : $i]:
% 9.07/9.23                (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 9.07/9.23                 | ~ (l1_pre_topc @ X52)
% 9.07/9.23                 | ~ (v2_pre_topc @ X52))))),
% 9.07/9.23      inference('sup-', [status(thm)], ['16', '17'])).
% 9.07/9.23  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf('21', plain,
% 9.07/9.23      (~
% 9.07/9.23       (![X51 : $i, X52 : $i]:
% 9.07/9.23          (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 9.07/9.23           | ~ (l1_pre_topc @ X52)
% 9.07/9.23           | ~ (v2_pre_topc @ X52)))),
% 9.07/9.23      inference('demod', [status(thm)], ['18', '19', '20'])).
% 9.07/9.23  thf('22', plain,
% 9.07/9.23      ((![X49 : $i, X50 : $i]:
% 9.07/9.23          (~ (l1_pre_topc @ X49)
% 9.07/9.23           | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 9.07/9.23           | ~ (v3_pre_topc @ X50 @ X49)
% 9.07/9.23           | ((k1_tops_1 @ X49 @ X50) = (X50)))) | 
% 9.07/9.23       (![X51 : $i, X52 : $i]:
% 9.07/9.23          (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 9.07/9.23           | ~ (l1_pre_topc @ X52)
% 9.07/9.23           | ~ (v2_pre_topc @ X52)))),
% 9.07/9.23      inference('split', [status(esa)], ['14'])).
% 9.07/9.23  thf('23', plain,
% 9.07/9.23      ((![X49 : $i, X50 : $i]:
% 9.07/9.23          (~ (l1_pre_topc @ X49)
% 9.07/9.23           | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 9.07/9.23           | ~ (v3_pre_topc @ X50 @ X49)
% 9.07/9.23           | ((k1_tops_1 @ X49 @ X50) = (X50))))),
% 9.07/9.23      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 9.07/9.23  thf('24', plain,
% 9.07/9.23      (![X49 : $i, X50 : $i]:
% 9.07/9.23         (~ (l1_pre_topc @ X49)
% 9.07/9.23          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 9.07/9.23          | ~ (v3_pre_topc @ X50 @ X49)
% 9.07/9.23          | ((k1_tops_1 @ X49 @ X50) = (X50)))),
% 9.07/9.23      inference('simpl_trail', [status(thm)], ['15', '23'])).
% 9.07/9.23  thf('25', plain,
% 9.07/9.23      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 9.07/9.23        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 9.07/9.23        | ~ (l1_pre_topc @ sk_A))),
% 9.07/9.23      inference('sup-', [status(thm)], ['13', '24'])).
% 9.07/9.23  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf('27', plain,
% 9.07/9.23      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 9.07/9.23      inference('demod', [status(thm)], ['25', '26'])).
% 9.07/9.23  thf('28', plain,
% 9.07/9.23      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 9.07/9.23         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 9.07/9.23      inference('sup-', [status(thm)], ['12', '27'])).
% 9.07/9.23  thf('29', plain,
% 9.07/9.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf(l78_tops_1, axiom,
% 9.07/9.23    (![A:$i]:
% 9.07/9.23     ( ( l1_pre_topc @ A ) =>
% 9.07/9.23       ( ![B:$i]:
% 9.07/9.23         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.07/9.23           ( ( k2_tops_1 @ A @ B ) =
% 9.07/9.23             ( k7_subset_1 @
% 9.07/9.23               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 9.07/9.23               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 9.07/9.23  thf('30', plain,
% 9.07/9.23      (![X47 : $i, X48 : $i]:
% 9.07/9.23         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 9.07/9.23          | ((k2_tops_1 @ X48 @ X47)
% 9.07/9.23              = (k7_subset_1 @ (u1_struct_0 @ X48) @ 
% 9.07/9.23                 (k2_pre_topc @ X48 @ X47) @ (k1_tops_1 @ X48 @ X47)))
% 9.07/9.23          | ~ (l1_pre_topc @ X48))),
% 9.07/9.23      inference('cnf', [status(esa)], [l78_tops_1])).
% 9.07/9.23  thf('31', plain,
% 9.07/9.23      ((~ (l1_pre_topc @ sk_A)
% 9.07/9.23        | ((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.23               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 9.07/9.23      inference('sup-', [status(thm)], ['29', '30'])).
% 9.07/9.23  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf('33', plain,
% 9.07/9.23      (((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 9.07/9.23            (k1_tops_1 @ sk_A @ sk_B)))),
% 9.07/9.23      inference('demod', [status(thm)], ['31', '32'])).
% 9.07/9.23  thf('34', plain,
% 9.07/9.23      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.23             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 9.07/9.23         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 9.07/9.23      inference('sup+', [status(thm)], ['28', '33'])).
% 9.07/9.23  thf('35', plain,
% 9.07/9.23      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.23              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 9.07/9.23         <= (~
% 9.07/9.23             (((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.23                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 9.07/9.23      inference('split', [status(esa)], ['10'])).
% 9.07/9.23  thf('36', plain,
% 9.07/9.23      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 9.07/9.23         <= (~
% 9.07/9.23             (((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.23                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 9.07/9.23             ((v3_pre_topc @ sk_B @ sk_A)))),
% 9.07/9.23      inference('sup-', [status(thm)], ['34', '35'])).
% 9.07/9.23  thf('37', plain,
% 9.07/9.23      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.23             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 9.07/9.23       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 9.07/9.23      inference('simplify', [status(thm)], ['36'])).
% 9.07/9.23  thf('38', plain,
% 9.07/9.23      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.23             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 9.07/9.23       ((v3_pre_topc @ sk_B @ sk_A))),
% 9.07/9.23      inference('split', [status(esa)], ['8'])).
% 9.07/9.23  thf('39', plain,
% 9.07/9.23      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.23             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 9.07/9.23      inference('sat_resolution*', [status(thm)], ['11', '37', '38'])).
% 9.07/9.23  thf('40', plain,
% 9.07/9.23      (((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 9.07/9.23            sk_B))),
% 9.07/9.23      inference('simpl_trail', [status(thm)], ['9', '39'])).
% 9.07/9.23  thf('41', plain,
% 9.07/9.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf(dt_k2_tops_1, axiom,
% 9.07/9.23    (![A:$i,B:$i]:
% 9.07/9.23     ( ( ( l1_pre_topc @ A ) & 
% 9.07/9.23         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 9.07/9.23       ( m1_subset_1 @
% 9.07/9.23         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 9.07/9.23  thf('42', plain,
% 9.07/9.23      (![X45 : $i, X46 : $i]:
% 9.07/9.23         (~ (l1_pre_topc @ X45)
% 9.07/9.23          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 9.07/9.23          | (m1_subset_1 @ (k2_tops_1 @ X45 @ X46) @ 
% 9.07/9.23             (k1_zfmisc_1 @ (u1_struct_0 @ X45))))),
% 9.07/9.23      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 9.07/9.23  thf('43', plain,
% 9.07/9.23      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.07/9.23         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.07/9.23        | ~ (l1_pre_topc @ sk_A))),
% 9.07/9.23      inference('sup-', [status(thm)], ['41', '42'])).
% 9.07/9.23  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf('45', plain,
% 9.07/9.23      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.07/9.23        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.07/9.23      inference('demod', [status(thm)], ['43', '44'])).
% 9.07/9.23  thf('46', plain,
% 9.07/9.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf(dt_k4_subset_1, axiom,
% 9.07/9.23    (![A:$i,B:$i,C:$i]:
% 9.07/9.23     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 9.07/9.23         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 9.07/9.23       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.07/9.23  thf('47', plain,
% 9.07/9.23      (![X32 : $i, X33 : $i, X34 : $i]:
% 9.07/9.23         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 9.07/9.23          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33))
% 9.07/9.23          | (m1_subset_1 @ (k4_subset_1 @ X33 @ X32 @ X34) @ 
% 9.07/9.23             (k1_zfmisc_1 @ X33)))),
% 9.07/9.23      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 9.07/9.23  thf('48', plain,
% 9.07/9.23      (![X0 : $i]:
% 9.07/9.23         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 9.07/9.23           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.07/9.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 9.07/9.23      inference('sup-', [status(thm)], ['46', '47'])).
% 9.07/9.23  thf('49', plain,
% 9.07/9.23      ((m1_subset_1 @ 
% 9.07/9.23        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 9.07/9.23        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.07/9.23      inference('sup-', [status(thm)], ['45', '48'])).
% 9.07/9.23  thf('50', plain,
% 9.07/9.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf(t65_tops_1, axiom,
% 9.07/9.23    (![A:$i]:
% 9.07/9.23     ( ( l1_pre_topc @ A ) =>
% 9.07/9.23       ( ![B:$i]:
% 9.07/9.23         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.07/9.23           ( ( k2_pre_topc @ A @ B ) =
% 9.07/9.23             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 9.07/9.23  thf('51', plain,
% 9.07/9.23      (![X55 : $i, X56 : $i]:
% 9.07/9.23         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 9.07/9.23          | ((k2_pre_topc @ X56 @ X55)
% 9.07/9.23              = (k4_subset_1 @ (u1_struct_0 @ X56) @ X55 @ 
% 9.07/9.23                 (k2_tops_1 @ X56 @ X55)))
% 9.07/9.23          | ~ (l1_pre_topc @ X56))),
% 9.07/9.23      inference('cnf', [status(esa)], [t65_tops_1])).
% 9.07/9.23  thf('52', plain,
% 9.07/9.23      ((~ (l1_pre_topc @ sk_A)
% 9.07/9.23        | ((k2_pre_topc @ sk_A @ sk_B)
% 9.07/9.23            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.07/9.23               (k2_tops_1 @ sk_A @ sk_B))))),
% 9.07/9.23      inference('sup-', [status(thm)], ['50', '51'])).
% 9.07/9.23  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf('54', plain,
% 9.07/9.23      (((k2_pre_topc @ sk_A @ sk_B)
% 9.07/9.23         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.07/9.23            (k2_tops_1 @ sk_A @ sk_B)))),
% 9.07/9.23      inference('demod', [status(thm)], ['52', '53'])).
% 9.07/9.23  thf('55', plain,
% 9.07/9.23      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 9.07/9.23        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.07/9.23      inference('demod', [status(thm)], ['49', '54'])).
% 9.07/9.23  thf('56', plain,
% 9.07/9.23      (![X37 : $i, X38 : $i, X39 : $i]:
% 9.07/9.23         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 9.07/9.23          | ((k7_subset_1 @ X38 @ X37 @ X39) = (k4_xboole_0 @ X37 @ X39)))),
% 9.07/9.23      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 9.07/9.23  thf('57', plain,
% 9.07/9.23      (![X0 : $i]:
% 9.07/9.23         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 9.07/9.23           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 9.07/9.23      inference('sup-', [status(thm)], ['55', '56'])).
% 9.07/9.23  thf('58', plain,
% 9.07/9.23      (((k2_tops_1 @ sk_A @ sk_B)
% 9.07/9.23         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 9.07/9.23      inference('demod', [status(thm)], ['40', '57'])).
% 9.07/9.23  thf(t100_xboole_1, axiom,
% 9.07/9.23    (![A:$i,B:$i]:
% 9.07/9.23     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 9.07/9.23  thf('59', plain,
% 9.07/9.23      (![X15 : $i, X16 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ X15 @ X16)
% 9.07/9.23           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 9.07/9.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 9.07/9.23  thf(t12_setfam_1, axiom,
% 9.07/9.23    (![A:$i,B:$i]:
% 9.07/9.23     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 9.07/9.23  thf('60', plain,
% 9.07/9.23      (![X40 : $i, X41 : $i]:
% 9.07/9.23         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 9.07/9.23      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.07/9.23  thf('61', plain,
% 9.07/9.23      (![X15 : $i, X16 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ X15 @ X16)
% 9.07/9.23           = (k5_xboole_0 @ X15 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16))))),
% 9.07/9.23      inference('demod', [status(thm)], ['59', '60'])).
% 9.07/9.23  thf(t112_xboole_1, axiom,
% 9.07/9.23    (![A:$i,B:$i,C:$i]:
% 9.07/9.23     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 9.07/9.23       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 9.07/9.23  thf('62', plain,
% 9.07/9.23      (![X17 : $i, X18 : $i, X19 : $i]:
% 9.07/9.23         ((k5_xboole_0 @ (k3_xboole_0 @ X17 @ X19) @ (k3_xboole_0 @ X18 @ X19))
% 9.07/9.23           = (k3_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19))),
% 9.07/9.23      inference('cnf', [status(esa)], [t112_xboole_1])).
% 9.07/9.23  thf('63', plain,
% 9.07/9.23      (![X40 : $i, X41 : $i]:
% 9.07/9.23         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 9.07/9.23      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.07/9.23  thf('64', plain,
% 9.07/9.23      (![X40 : $i, X41 : $i]:
% 9.07/9.23         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 9.07/9.23      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.07/9.23  thf('65', plain,
% 9.07/9.23      (![X40 : $i, X41 : $i]:
% 9.07/9.23         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 9.07/9.23      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.07/9.23  thf('66', plain,
% 9.07/9.23      (![X17 : $i, X18 : $i, X19 : $i]:
% 9.07/9.23         ((k5_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X17 @ X19)) @ 
% 9.07/9.23           (k1_setfam_1 @ (k2_tarski @ X18 @ X19)))
% 9.07/9.23           = (k1_setfam_1 @ (k2_tarski @ (k5_xboole_0 @ X17 @ X18) @ X19)))),
% 9.07/9.23      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 9.07/9.23  thf('67', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)
% 9.07/9.23           = (k1_setfam_1 @ 
% 9.07/9.23              (k2_tarski @ 
% 9.07/9.23               (k5_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ X0)))),
% 9.07/9.23      inference('sup+', [status(thm)], ['61', '66'])).
% 9.07/9.23  thf('68', plain,
% 9.07/9.23      (![X15 : $i, X16 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ X15 @ X16)
% 9.07/9.23           = (k5_xboole_0 @ X15 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16))))),
% 9.07/9.23      inference('demod', [status(thm)], ['59', '60'])).
% 9.07/9.23  thf(commutativity_k2_tarski, axiom,
% 9.07/9.23    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 9.07/9.23  thf('69', plain,
% 9.07/9.23      (![X26 : $i, X27 : $i]:
% 9.07/9.23         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 9.07/9.23      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 9.07/9.23  thf('70', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)
% 9.07/9.23           = (k1_setfam_1 @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 9.07/9.23      inference('demod', [status(thm)], ['67', '68', '69'])).
% 9.07/9.23  thf(d4_xboole_0, axiom,
% 9.07/9.23    (![A:$i,B:$i,C:$i]:
% 9.07/9.23     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 9.07/9.23       ( ![D:$i]:
% 9.07/9.23         ( ( r2_hidden @ D @ C ) <=>
% 9.07/9.23           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 9.07/9.23  thf('71', plain,
% 9.07/9.23      (![X1 : $i, X2 : $i, X5 : $i]:
% 9.07/9.23         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 9.07/9.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 9.07/9.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 9.07/9.23      inference('cnf', [status(esa)], [d4_xboole_0])).
% 9.07/9.23  thf('72', plain,
% 9.07/9.23      (![X40 : $i, X41 : $i]:
% 9.07/9.23         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 9.07/9.23      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.07/9.23  thf('73', plain,
% 9.07/9.23      (![X1 : $i, X2 : $i, X5 : $i]:
% 9.07/9.23         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 9.07/9.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 9.07/9.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 9.07/9.23      inference('demod', [status(thm)], ['71', '72'])).
% 9.07/9.23  thf(t3_boole, axiom,
% 9.07/9.23    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 9.07/9.23  thf('74', plain, (![X25 : $i]: ((k4_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 9.07/9.23      inference('cnf', [status(esa)], [t3_boole])).
% 9.07/9.23  thf(d5_xboole_0, axiom,
% 9.07/9.23    (![A:$i,B:$i,C:$i]:
% 9.07/9.23     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 9.07/9.23       ( ![D:$i]:
% 9.07/9.23         ( ( r2_hidden @ D @ C ) <=>
% 9.07/9.23           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 9.07/9.23  thf('75', plain,
% 9.07/9.23      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 9.07/9.23         (~ (r2_hidden @ X10 @ X9)
% 9.07/9.23          | ~ (r2_hidden @ X10 @ X8)
% 9.07/9.23          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 9.07/9.23      inference('cnf', [status(esa)], [d5_xboole_0])).
% 9.07/9.23  thf('76', plain,
% 9.07/9.23      (![X7 : $i, X8 : $i, X10 : $i]:
% 9.07/9.23         (~ (r2_hidden @ X10 @ X8)
% 9.07/9.23          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 9.07/9.23      inference('simplify', [status(thm)], ['75'])).
% 9.07/9.23  thf('77', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 9.07/9.23      inference('sup-', [status(thm)], ['74', '76'])).
% 9.07/9.23  thf('78', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 9.07/9.23      inference('condensation', [status(thm)], ['77'])).
% 9.07/9.23  thf('79', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 9.07/9.23          | ((X1) = (k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0))))),
% 9.07/9.23      inference('sup-', [status(thm)], ['73', '78'])).
% 9.07/9.23  thf('80', plain,
% 9.07/9.23      (![X26 : $i, X27 : $i]:
% 9.07/9.23         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 9.07/9.23      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 9.07/9.23  thf(t2_boole, axiom,
% 9.07/9.23    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 9.07/9.23  thf('81', plain,
% 9.07/9.23      (![X22 : $i]: ((k3_xboole_0 @ X22 @ k1_xboole_0) = (k1_xboole_0))),
% 9.07/9.23      inference('cnf', [status(esa)], [t2_boole])).
% 9.07/9.23  thf('82', plain,
% 9.07/9.23      (![X40 : $i, X41 : $i]:
% 9.07/9.23         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 9.07/9.23      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.07/9.23  thf('83', plain,
% 9.07/9.23      (![X22 : $i]:
% 9.07/9.23         ((k1_setfam_1 @ (k2_tarski @ X22 @ k1_xboole_0)) = (k1_xboole_0))),
% 9.07/9.23      inference('demod', [status(thm)], ['81', '82'])).
% 9.07/9.23  thf('84', plain,
% 9.07/9.23      (![X0 : $i]:
% 9.07/9.23         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 9.07/9.23      inference('sup+', [status(thm)], ['80', '83'])).
% 9.07/9.23  thf('85', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 9.07/9.23          | ((X1) = (k1_xboole_0)))),
% 9.07/9.23      inference('demod', [status(thm)], ['79', '84'])).
% 9.07/9.23  thf('86', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)
% 9.07/9.23           = (k1_setfam_1 @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 9.07/9.23      inference('demod', [status(thm)], ['67', '68', '69'])).
% 9.07/9.23  thf('87', plain,
% 9.07/9.23      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 9.07/9.23         (~ (r2_hidden @ X4 @ X3)
% 9.07/9.23          | (r2_hidden @ X4 @ X1)
% 9.07/9.23          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 9.07/9.23      inference('cnf', [status(esa)], [d4_xboole_0])).
% 9.07/9.23  thf('88', plain,
% 9.07/9.23      (![X1 : $i, X2 : $i, X4 : $i]:
% 9.07/9.23         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 9.07/9.23      inference('simplify', [status(thm)], ['87'])).
% 9.07/9.23  thf('89', plain,
% 9.07/9.23      (![X40 : $i, X41 : $i]:
% 9.07/9.23         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 9.07/9.23      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.07/9.23  thf('90', plain,
% 9.07/9.23      (![X1 : $i, X2 : $i, X4 : $i]:
% 9.07/9.23         ((r2_hidden @ X4 @ X1)
% 9.07/9.23          | ~ (r2_hidden @ X4 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))))),
% 9.07/9.23      inference('demod', [status(thm)], ['88', '89'])).
% 9.07/9.23  thf('91', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.07/9.23         (~ (r2_hidden @ X2 @ 
% 9.07/9.23             (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0))
% 9.07/9.23          | (r2_hidden @ X2 @ X0))),
% 9.07/9.23      inference('sup-', [status(thm)], ['86', '90'])).
% 9.07/9.23  thf('92', plain,
% 9.07/9.23      (![X7 : $i, X8 : $i, X10 : $i]:
% 9.07/9.23         (~ (r2_hidden @ X10 @ X8)
% 9.07/9.23          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 9.07/9.23      inference('simplify', [status(thm)], ['75'])).
% 9.07/9.23  thf('93', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.07/9.23         ~ (r2_hidden @ X2 @ 
% 9.07/9.23            (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0))),
% 9.07/9.23      inference('clc', [status(thm)], ['91', '92'])).
% 9.07/9.23  thf('94', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)
% 9.07/9.23           = (k1_xboole_0))),
% 9.07/9.23      inference('sup-', [status(thm)], ['85', '93'])).
% 9.07/9.23  thf('95', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((k1_xboole_0)
% 9.07/9.23           = (k1_setfam_1 @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 9.07/9.23      inference('demod', [status(thm)], ['70', '94'])).
% 9.07/9.23  thf('96', plain,
% 9.07/9.23      (![X15 : $i, X16 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ X15 @ X16)
% 9.07/9.23           = (k5_xboole_0 @ X15 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16))))),
% 9.07/9.23      inference('demod', [status(thm)], ['59', '60'])).
% 9.07/9.23  thf('97', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 9.07/9.23           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 9.07/9.23      inference('sup+', [status(thm)], ['95', '96'])).
% 9.07/9.23  thf('98', plain,
% 9.07/9.23      (![X22 : $i]:
% 9.07/9.23         ((k1_setfam_1 @ (k2_tarski @ X22 @ k1_xboole_0)) = (k1_xboole_0))),
% 9.07/9.23      inference('demod', [status(thm)], ['81', '82'])).
% 9.07/9.23  thf('99', plain,
% 9.07/9.23      (![X15 : $i, X16 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ X15 @ X16)
% 9.07/9.23           = (k5_xboole_0 @ X15 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16))))),
% 9.07/9.23      inference('demod', [status(thm)], ['59', '60'])).
% 9.07/9.23  thf('100', plain,
% 9.07/9.23      (![X0 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 9.07/9.23      inference('sup+', [status(thm)], ['98', '99'])).
% 9.07/9.23  thf('101', plain, (![X25 : $i]: ((k4_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 9.07/9.23      inference('cnf', [status(esa)], [t3_boole])).
% 9.07/9.23  thf('102', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 9.07/9.23      inference('sup+', [status(thm)], ['100', '101'])).
% 9.07/9.23  thf('103', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 9.07/9.23      inference('demod', [status(thm)], ['97', '102'])).
% 9.07/9.23  thf('104', plain,
% 9.07/9.23      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 9.07/9.23      inference('sup+', [status(thm)], ['58', '103'])).
% 9.07/9.23  thf('105', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 9.07/9.23      inference('sup+', [status(thm)], ['7', '104'])).
% 9.07/9.23  thf('106', plain,
% 9.07/9.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.07/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.23  thf(t3_subset, axiom,
% 9.07/9.23    (![A:$i,B:$i]:
% 9.07/9.23     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 9.07/9.23  thf('107', plain,
% 9.07/9.23      (![X42 : $i, X43 : $i]:
% 9.07/9.23         ((r1_tarski @ X42 @ X43) | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43)))),
% 9.07/9.23      inference('cnf', [status(esa)], [t3_subset])).
% 9.07/9.23  thf('108', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 9.07/9.23      inference('sup-', [status(thm)], ['106', '107'])).
% 9.07/9.23  thf(t28_xboole_1, axiom,
% 9.07/9.23    (![A:$i,B:$i]:
% 9.07/9.23     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 9.07/9.23  thf('109', plain,
% 9.07/9.23      (![X20 : $i, X21 : $i]:
% 9.07/9.23         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 9.07/9.23      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.07/9.23  thf('110', plain,
% 9.07/9.23      (![X40 : $i, X41 : $i]:
% 9.07/9.23         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 9.07/9.23      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.07/9.23  thf('111', plain,
% 9.07/9.23      (![X20 : $i, X21 : $i]:
% 9.07/9.23         (((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (X20))
% 9.07/9.23          | ~ (r1_tarski @ X20 @ X21))),
% 9.07/9.23      inference('demod', [status(thm)], ['109', '110'])).
% 9.07/9.23  thf('112', plain,
% 9.07/9.23      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 9.07/9.23      inference('sup-', [status(thm)], ['108', '111'])).
% 9.07/9.23  thf('113', plain,
% 9.07/9.23      (![X26 : $i, X27 : $i]:
% 9.07/9.23         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 9.07/9.23      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 9.07/9.23  thf('114', plain,
% 9.07/9.23      (![X15 : $i, X16 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ X15 @ X16)
% 9.07/9.23           = (k5_xboole_0 @ X15 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16))))),
% 9.07/9.23      inference('demod', [status(thm)], ['59', '60'])).
% 9.07/9.23  thf('115', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ X0 @ X1)
% 9.07/9.23           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 9.07/9.23      inference('sup+', [status(thm)], ['113', '114'])).
% 9.07/9.23  thf('116', plain,
% 9.07/9.23      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 9.07/9.23         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 9.07/9.23      inference('sup+', [status(thm)], ['112', '115'])).
% 9.07/9.23  thf(t36_xboole_1, axiom,
% 9.07/9.23    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 9.07/9.23  thf('117', plain,
% 9.07/9.23      (![X23 : $i, X24 : $i]: (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X23)),
% 9.07/9.23      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.07/9.23  thf('118', plain,
% 9.07/9.23      (![X20 : $i, X21 : $i]:
% 9.07/9.23         (((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (X20))
% 9.07/9.23          | ~ (r1_tarski @ X20 @ X21))),
% 9.07/9.23      inference('demod', [status(thm)], ['109', '110'])).
% 9.07/9.23  thf('119', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((k1_setfam_1 @ (k2_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 9.07/9.23           = (k4_xboole_0 @ X0 @ X1))),
% 9.07/9.23      inference('sup-', [status(thm)], ['117', '118'])).
% 9.07/9.23  thf('120', plain,
% 9.07/9.23      (![X26 : $i, X27 : $i]:
% 9.07/9.23         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 9.07/9.23      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 9.07/9.23  thf('121', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((k1_setfam_1 @ (k2_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 9.07/9.23           = (k4_xboole_0 @ X0 @ X1))),
% 9.07/9.23      inference('demod', [status(thm)], ['119', '120'])).
% 9.07/9.23  thf('122', plain,
% 9.07/9.23      (![X15 : $i, X16 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ X15 @ X16)
% 9.07/9.23           = (k5_xboole_0 @ X15 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16))))),
% 9.07/9.23      inference('demod', [status(thm)], ['59', '60'])).
% 9.07/9.23  thf('123', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.07/9.23           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 9.07/9.23      inference('sup+', [status(thm)], ['121', '122'])).
% 9.07/9.23  thf('124', plain,
% 9.07/9.23      (![X23 : $i, X24 : $i]: (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X23)),
% 9.07/9.23      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.07/9.23  thf('125', plain,
% 9.07/9.23      (![X42 : $i, X44 : $i]:
% 9.07/9.23         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 9.07/9.23      inference('cnf', [status(esa)], [t3_subset])).
% 9.07/9.23  thf('126', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 9.07/9.23      inference('sup-', [status(thm)], ['124', '125'])).
% 9.07/9.23  thf(d5_subset_1, axiom,
% 9.07/9.23    (![A:$i,B:$i]:
% 9.07/9.23     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.07/9.23       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 9.07/9.23  thf('127', plain,
% 9.07/9.23      (![X28 : $i, X29 : $i]:
% 9.07/9.23         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 9.07/9.23          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 9.07/9.23      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.07/9.23  thf('128', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 9.07/9.23           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 9.07/9.23      inference('sup-', [status(thm)], ['126', '127'])).
% 9.07/9.23  thf('129', plain,
% 9.07/9.23      (![X0 : $i, X1 : $i]:
% 9.07/9.23         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.07/9.23           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 9.07/9.23      inference('sup+', [status(thm)], ['123', '128'])).
% 9.07/9.24  thf(idempotence_k3_xboole_0, axiom,
% 9.07/9.24    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 9.07/9.24  thf('130', plain, (![X12 : $i]: ((k3_xboole_0 @ X12 @ X12) = (X12))),
% 9.07/9.24      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 9.07/9.24  thf('131', plain,
% 9.07/9.24      (![X40 : $i, X41 : $i]:
% 9.07/9.24         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 9.07/9.24      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.07/9.24  thf('132', plain,
% 9.07/9.24      (![X12 : $i]: ((k1_setfam_1 @ (k2_tarski @ X12 @ X12)) = (X12))),
% 9.07/9.24      inference('demod', [status(thm)], ['130', '131'])).
% 9.07/9.24  thf('133', plain,
% 9.07/9.24      (![X17 : $i, X18 : $i, X19 : $i]:
% 9.07/9.24         ((k5_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X17 @ X19)) @ 
% 9.07/9.24           (k1_setfam_1 @ (k2_tarski @ X18 @ X19)))
% 9.07/9.24           = (k1_setfam_1 @ (k2_tarski @ (k5_xboole_0 @ X17 @ X18) @ X19)))),
% 9.07/9.24      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 9.07/9.24  thf('134', plain,
% 9.07/9.24      (![X0 : $i, X1 : $i]:
% 9.07/9.24         ((k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 9.07/9.24           = (k1_setfam_1 @ (k2_tarski @ (k5_xboole_0 @ X0 @ X1) @ X0)))),
% 9.07/9.24      inference('sup+', [status(thm)], ['132', '133'])).
% 9.07/9.24  thf('135', plain,
% 9.07/9.24      (![X0 : $i, X1 : $i]:
% 9.07/9.24         ((k4_xboole_0 @ X0 @ X1)
% 9.07/9.24           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 9.07/9.24      inference('sup+', [status(thm)], ['113', '114'])).
% 9.07/9.24  thf('136', plain,
% 9.07/9.24      (![X26 : $i, X27 : $i]:
% 9.07/9.24         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 9.07/9.24      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 9.07/9.24  thf('137', plain,
% 9.07/9.24      (![X0 : $i, X1 : $i]:
% 9.07/9.24         ((k4_xboole_0 @ X0 @ X1)
% 9.07/9.24           = (k1_setfam_1 @ (k2_tarski @ X0 @ (k5_xboole_0 @ X0 @ X1))))),
% 9.07/9.24      inference('demod', [status(thm)], ['134', '135', '136'])).
% 9.07/9.24  thf('138', plain,
% 9.07/9.24      (![X15 : $i, X16 : $i]:
% 9.07/9.24         ((k4_xboole_0 @ X15 @ X16)
% 9.07/9.24           = (k5_xboole_0 @ X15 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16))))),
% 9.07/9.24      inference('demod', [status(thm)], ['59', '60'])).
% 9.07/9.24  thf('139', plain,
% 9.07/9.24      (![X0 : $i, X1 : $i]:
% 9.07/9.24         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 9.07/9.24           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 9.07/9.24      inference('sup+', [status(thm)], ['137', '138'])).
% 9.07/9.24  thf('140', plain,
% 9.07/9.24      (![X0 : $i, X1 : $i]:
% 9.07/9.24         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.07/9.24           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 9.07/9.24      inference('demod', [status(thm)], ['129', '139'])).
% 9.07/9.24  thf('141', plain,
% 9.07/9.24      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.24         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 9.07/9.24         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.24            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 9.07/9.24      inference('sup+', [status(thm)], ['116', '140'])).
% 9.07/9.24  thf('142', plain,
% 9.07/9.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.07/9.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.24  thf(involutiveness_k3_subset_1, axiom,
% 9.07/9.24    (![A:$i,B:$i]:
% 9.07/9.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.07/9.24       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 9.07/9.24  thf('143', plain,
% 9.07/9.24      (![X35 : $i, X36 : $i]:
% 9.07/9.24         (((k3_subset_1 @ X36 @ (k3_subset_1 @ X36 @ X35)) = (X35))
% 9.07/9.24          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 9.07/9.24      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 9.07/9.24  thf('144', plain,
% 9.07/9.24      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.24         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 9.07/9.24      inference('sup-', [status(thm)], ['142', '143'])).
% 9.07/9.24  thf('145', plain,
% 9.07/9.24      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 9.07/9.24         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 9.07/9.24      inference('sup+', [status(thm)], ['112', '115'])).
% 9.07/9.24  thf('146', plain,
% 9.07/9.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.07/9.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.24  thf('147', plain,
% 9.07/9.24      (![X28 : $i, X29 : $i]:
% 9.07/9.24         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 9.07/9.24          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 9.07/9.24      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.07/9.24  thf('148', plain,
% 9.07/9.24      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 9.07/9.24         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 9.07/9.24      inference('sup-', [status(thm)], ['146', '147'])).
% 9.07/9.24  thf('149', plain,
% 9.07/9.24      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 9.07/9.24         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 9.07/9.24      inference('sup+', [status(thm)], ['145', '148'])).
% 9.07/9.24  thf('150', plain,
% 9.07/9.24      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.24         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 9.07/9.24      inference('demod', [status(thm)], ['144', '149'])).
% 9.07/9.24  thf('151', plain,
% 9.07/9.24      (((sk_B)
% 9.07/9.24         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.24            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 9.07/9.24      inference('demod', [status(thm)], ['141', '150'])).
% 9.07/9.24  thf('152', plain,
% 9.07/9.24      (![X0 : $i, X1 : $i]:
% 9.07/9.24         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 9.07/9.24      inference('sup-', [status(thm)], ['124', '125'])).
% 9.07/9.24  thf('153', plain,
% 9.07/9.24      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 9.07/9.24         (~ (l1_pre_topc @ X49)
% 9.07/9.24          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 9.07/9.24          | ((k1_tops_1 @ X52 @ X51) != (X51))
% 9.07/9.24          | (v3_pre_topc @ X51 @ X52)
% 9.07/9.24          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 9.07/9.24          | ~ (l1_pre_topc @ X52)
% 9.07/9.24          | ~ (v2_pre_topc @ X52))),
% 9.07/9.24      inference('cnf', [status(esa)], [t55_tops_1])).
% 9.07/9.24  thf('154', plain,
% 9.07/9.24      ((![X51 : $i, X52 : $i]:
% 9.07/9.24          (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 9.07/9.24           | ~ (l1_pre_topc @ X52)
% 9.07/9.24           | ~ (v2_pre_topc @ X52)
% 9.07/9.24           | ((k1_tops_1 @ X52 @ X51) != (X51))
% 9.07/9.24           | (v3_pre_topc @ X51 @ X52)))
% 9.07/9.24         <= ((![X51 : $i, X52 : $i]:
% 9.07/9.24                (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 9.07/9.24                 | ~ (l1_pre_topc @ X52)
% 9.07/9.24                 | ~ (v2_pre_topc @ X52)
% 9.07/9.24                 | ((k1_tops_1 @ X52 @ X51) != (X51))
% 9.07/9.24                 | (v3_pre_topc @ X51 @ X52))))),
% 9.07/9.24      inference('split', [status(esa)], ['153'])).
% 9.07/9.24  thf('155', plain,
% 9.07/9.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.07/9.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.24  thf('156', plain,
% 9.07/9.24      ((![X49 : $i, X50 : $i]:
% 9.07/9.24          (~ (l1_pre_topc @ X49)
% 9.07/9.24           | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))))
% 9.07/9.24         <= ((![X49 : $i, X50 : $i]:
% 9.07/9.24                (~ (l1_pre_topc @ X49)
% 9.07/9.24                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49))))))),
% 9.07/9.24      inference('split', [status(esa)], ['153'])).
% 9.07/9.24  thf('157', plain,
% 9.07/9.24      ((~ (l1_pre_topc @ sk_A))
% 9.07/9.24         <= ((![X49 : $i, X50 : $i]:
% 9.07/9.24                (~ (l1_pre_topc @ X49)
% 9.07/9.24                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49))))))),
% 9.07/9.24      inference('sup-', [status(thm)], ['155', '156'])).
% 9.07/9.24  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 9.07/9.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.24  thf('159', plain,
% 9.07/9.24      (~
% 9.07/9.24       (![X49 : $i, X50 : $i]:
% 9.07/9.24          (~ (l1_pre_topc @ X49)
% 9.07/9.24           | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))))),
% 9.07/9.24      inference('demod', [status(thm)], ['157', '158'])).
% 9.07/9.24  thf('160', plain,
% 9.07/9.24      ((![X51 : $i, X52 : $i]:
% 9.07/9.24          (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 9.07/9.24           | ~ (l1_pre_topc @ X52)
% 9.07/9.24           | ~ (v2_pre_topc @ X52)
% 9.07/9.24           | ((k1_tops_1 @ X52 @ X51) != (X51))
% 9.07/9.24           | (v3_pre_topc @ X51 @ X52))) | 
% 9.07/9.24       (![X49 : $i, X50 : $i]:
% 9.07/9.24          (~ (l1_pre_topc @ X49)
% 9.07/9.24           | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))))),
% 9.07/9.24      inference('split', [status(esa)], ['153'])).
% 9.07/9.24  thf('161', plain,
% 9.07/9.24      ((![X51 : $i, X52 : $i]:
% 9.07/9.24          (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 9.07/9.24           | ~ (l1_pre_topc @ X52)
% 9.07/9.24           | ~ (v2_pre_topc @ X52)
% 9.07/9.24           | ((k1_tops_1 @ X52 @ X51) != (X51))
% 9.07/9.24           | (v3_pre_topc @ X51 @ X52)))),
% 9.07/9.24      inference('sat_resolution*', [status(thm)], ['159', '160'])).
% 9.07/9.24  thf('162', plain,
% 9.07/9.24      (![X51 : $i, X52 : $i]:
% 9.07/9.24         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 9.07/9.24          | ~ (l1_pre_topc @ X52)
% 9.07/9.24          | ~ (v2_pre_topc @ X52)
% 9.07/9.24          | ((k1_tops_1 @ X52 @ X51) != (X51))
% 9.07/9.24          | (v3_pre_topc @ X51 @ X52))),
% 9.07/9.24      inference('simpl_trail', [status(thm)], ['154', '161'])).
% 9.07/9.24  thf('163', plain,
% 9.07/9.24      (![X0 : $i, X1 : $i]:
% 9.07/9.24         ((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 9.07/9.24          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 9.07/9.24              != (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 9.07/9.24          | ~ (v2_pre_topc @ X0)
% 9.07/9.24          | ~ (l1_pre_topc @ X0))),
% 9.07/9.24      inference('sup-', [status(thm)], ['152', '162'])).
% 9.07/9.24  thf('164', plain,
% 9.07/9.24      ((((k1_tops_1 @ sk_A @ sk_B)
% 9.07/9.24          != (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.24              (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 9.07/9.24        | ~ (l1_pre_topc @ sk_A)
% 9.07/9.24        | ~ (v2_pre_topc @ sk_A)
% 9.07/9.24        | (v3_pre_topc @ 
% 9.07/9.24           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.24            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 9.07/9.24           sk_A))),
% 9.07/9.24      inference('sup-', [status(thm)], ['151', '163'])).
% 9.07/9.24  thf('165', plain,
% 9.07/9.24      (((sk_B)
% 9.07/9.24         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.24            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 9.07/9.24      inference('demod', [status(thm)], ['141', '150'])).
% 9.07/9.24  thf('166', plain, ((l1_pre_topc @ sk_A)),
% 9.07/9.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.24  thf('167', plain, ((v2_pre_topc @ sk_A)),
% 9.07/9.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.07/9.24  thf('168', plain,
% 9.07/9.24      (((sk_B)
% 9.07/9.24         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 9.07/9.24            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 9.07/9.24      inference('demod', [status(thm)], ['141', '150'])).
% 9.07/9.24  thf('169', plain,
% 9.07/9.24      ((((k1_tops_1 @ sk_A @ sk_B) != (sk_B)) | (v3_pre_topc @ sk_B @ sk_A))),
% 9.07/9.24      inference('demod', [status(thm)], ['164', '165', '166', '167', '168'])).
% 9.07/9.24  thf('170', plain,
% 9.07/9.24      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 9.07/9.24      inference('split', [status(esa)], ['10'])).
% 9.07/9.24  thf('171', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 9.07/9.24      inference('sat_resolution*', [status(thm)], ['11', '37'])).
% 9.07/9.24  thf('172', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 9.07/9.24      inference('simpl_trail', [status(thm)], ['170', '171'])).
% 9.07/9.24  thf('173', plain, (((k1_tops_1 @ sk_A @ sk_B) != (sk_B))),
% 9.07/9.24      inference('clc', [status(thm)], ['169', '172'])).
% 9.07/9.24  thf('174', plain, ($false),
% 9.07/9.24      inference('simplify_reflect-', [status(thm)], ['105', '173'])).
% 9.07/9.24  
% 9.07/9.24  % SZS output end Refutation
% 9.07/9.24  
% 9.07/9.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
