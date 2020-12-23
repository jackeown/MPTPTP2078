%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2Z8KmdOxDH

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:28 EST 2020

% Result     : Theorem 51.08s
% Output     : Refutation 51.08s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 574 expanded)
%              Number of leaves         :   43 ( 186 expanded)
%              Depth                    :   18
%              Number of atoms          : 1788 (6750 expanded)
%              Number of equality atoms :  129 ( 455 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( ( k1_tops_1 @ X59 @ X58 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X59 ) @ X58 @ ( k2_tops_1 @ X59 @ X58 ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k4_xboole_0 @ X38 @ X40 ) ) ) ),
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
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( l1_pre_topc @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( v3_pre_topc @ X51 @ X50 )
      | ( ( k1_tops_1 @ X50 @ X51 )
        = X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( v2_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('15',plain,
    ( ! [X50: $i,X51: $i] :
        ( ~ ( l1_pre_topc @ X50 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
        | ~ ( v3_pre_topc @ X51 @ X50 )
        | ( ( k1_tops_1 @ X50 @ X51 )
          = X51 ) )
   <= ! [X50: $i,X51: $i] :
        ( ~ ( l1_pre_topc @ X50 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
        | ~ ( v3_pre_topc @ X51 @ X50 )
        | ( ( k1_tops_1 @ X50 @ X51 )
          = X51 ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ! [X52: $i,X53: $i] :
        ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
        | ~ ( l1_pre_topc @ X53 )
        | ~ ( v2_pre_topc @ X53 ) )
   <= ! [X52: $i,X53: $i] :
        ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
        | ~ ( l1_pre_topc @ X53 )
        | ~ ( v2_pre_topc @ X53 ) ) ),
    inference(split,[status(esa)],['14'])).

thf('18',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X52: $i,X53: $i] :
        ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
        | ~ ( l1_pre_topc @ X53 )
        | ~ ( v2_pre_topc @ X53 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ~ ! [X52: $i,X53: $i] :
        ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
        | ~ ( l1_pre_topc @ X53 )
        | ~ ( v2_pre_topc @ X53 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ! [X50: $i,X51: $i] :
        ( ~ ( l1_pre_topc @ X50 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
        | ~ ( v3_pre_topc @ X51 @ X50 )
        | ( ( k1_tops_1 @ X50 @ X51 )
          = X51 ) )
    | ! [X52: $i,X53: $i] :
        ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
        | ~ ( l1_pre_topc @ X53 )
        | ~ ( v2_pre_topc @ X53 ) ) ),
    inference(split,[status(esa)],['14'])).

thf('23',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( l1_pre_topc @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( v3_pre_topc @ X51 @ X50 )
      | ( ( k1_tops_1 @ X50 @ X51 )
        = X51 ) ) ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( l1_pre_topc @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( v3_pre_topc @ X51 @ X50 )
      | ( ( k1_tops_1 @ X50 @ X51 )
        = X51 ) ) ),
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
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k2_tops_1 @ X49 @ X48 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X49 ) @ ( k2_pre_topc @ X49 @ X48 ) @ ( k1_tops_1 @ X49 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
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
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X31 @ X30 @ X32 ) @ ( k1_zfmisc_1 @ X31 ) ) ) ),
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
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( ( k2_pre_topc @ X57 @ X56 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X57 ) @ X56 @ ( k2_tops_1 @ X57 @ X56 ) ) )
      | ~ ( l1_pre_topc @ X57 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k4_xboole_0 @ X38 @ X40 ) ) ) ),
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

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('62',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k3_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('63',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('64',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('65',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('66',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('67',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) @ X8 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['61','67'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('69',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('70',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('71',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('72',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      = ( k5_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('75',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('78',plain,(
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('81',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('83',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','83'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('85',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('86',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('87',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('88',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) ) )
      = ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) ) @ X20 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X1 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['84','90'])).

thf('92',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('93',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('94',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('95',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('96',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('97',plain,(
    ! [X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['91','98'])).

thf('100',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['58','99'])).

thf('101',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['7','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('103',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r1_tarski @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('104',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('105',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('106',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('107',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('110',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('112',plain,(
    ! [X43: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('114',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['110','115'])).

thf('117',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('118',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('120',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X34 @ ( k3_subset_1 @ X34 @ X33 ) )
        = X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('121',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('125',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['121','126'])).

thf('128',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['118','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('130',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( l1_pre_topc @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( ( k1_tops_1 @ X53 @ X52 )
       != X52 )
      | ( v3_pre_topc @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( v2_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('131',plain,
    ( ! [X52: $i,X53: $i] :
        ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
        | ~ ( l1_pre_topc @ X53 )
        | ~ ( v2_pre_topc @ X53 )
        | ( ( k1_tops_1 @ X53 @ X52 )
         != X52 )
        | ( v3_pre_topc @ X52 @ X53 ) )
   <= ! [X52: $i,X53: $i] :
        ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
        | ~ ( l1_pre_topc @ X53 )
        | ~ ( v2_pre_topc @ X53 )
        | ( ( k1_tops_1 @ X53 @ X52 )
         != X52 )
        | ( v3_pre_topc @ X52 @ X53 ) ) ),
    inference(split,[status(esa)],['130'])).

thf('132',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ! [X50: $i,X51: $i] :
        ( ~ ( l1_pre_topc @ X50 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) )
   <= ! [X50: $i,X51: $i] :
        ( ~ ( l1_pre_topc @ X50 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) ) ),
    inference(split,[status(esa)],['130'])).

thf('134',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X50: $i,X51: $i] :
        ( ~ ( l1_pre_topc @ X50 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ~ ! [X50: $i,X51: $i] :
        ( ~ ( l1_pre_topc @ X50 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ! [X52: $i,X53: $i] :
        ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
        | ~ ( l1_pre_topc @ X53 )
        | ~ ( v2_pre_topc @ X53 )
        | ( ( k1_tops_1 @ X53 @ X52 )
         != X52 )
        | ( v3_pre_topc @ X52 @ X53 ) )
    | ! [X50: $i,X51: $i] :
        ( ~ ( l1_pre_topc @ X50 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) ) ),
    inference(split,[status(esa)],['130'])).

thf('138',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( v2_pre_topc @ X53 )
      | ( ( k1_tops_1 @ X53 @ X52 )
       != X52 )
      | ( v3_pre_topc @ X52 @ X53 ) ) ),
    inference('sat_resolution*',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( v2_pre_topc @ X53 )
      | ( ( k1_tops_1 @ X53 @ X52 )
       != X52 )
      | ( v3_pre_topc @ X52 @ X53 ) ) ),
    inference(simpl_trail,[status(thm)],['131','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
       != ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','139'])).

thf('141',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['128','140'])).

thf('142',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['118','127'])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['118','127'])).

thf('146',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['141','142','143','144','145'])).

thf('147',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('148',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['11','37'])).

thf('149',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['147','148'])).

thf('150',plain,(
    ( k1_tops_1 @ sk_A @ sk_B )
 != sk_B ),
    inference(clc,[status(thm)],['146','149'])).

thf('151',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['101','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2Z8KmdOxDH
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 51.08/51.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 51.08/51.28  % Solved by: fo/fo7.sh
% 51.08/51.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 51.08/51.28  % done 35138 iterations in 50.817s
% 51.08/51.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 51.08/51.28  % SZS output start Refutation
% 51.08/51.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 51.08/51.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 51.08/51.28  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 51.08/51.28  thf(sk_A_type, type, sk_A: $i).
% 51.08/51.28  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 51.08/51.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 51.08/51.28  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 51.08/51.28  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 51.08/51.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 51.08/51.28  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 51.08/51.28  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 51.08/51.28  thf(sk_B_type, type, sk_B: $i).
% 51.08/51.28  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 51.08/51.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 51.08/51.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 51.08/51.28  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 51.08/51.28  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 51.08/51.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 51.08/51.28  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 51.08/51.28  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 51.08/51.28  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 51.08/51.28  thf(t76_tops_1, conjecture,
% 51.08/51.28    (![A:$i]:
% 51.08/51.28     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 51.08/51.28       ( ![B:$i]:
% 51.08/51.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.08/51.28           ( ( v3_pre_topc @ B @ A ) <=>
% 51.08/51.28             ( ( k2_tops_1 @ A @ B ) =
% 51.08/51.28               ( k7_subset_1 @
% 51.08/51.28                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 51.08/51.28  thf(zf_stmt_0, negated_conjecture,
% 51.08/51.28    (~( ![A:$i]:
% 51.08/51.28        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 51.08/51.28          ( ![B:$i]:
% 51.08/51.28            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.08/51.28              ( ( v3_pre_topc @ B @ A ) <=>
% 51.08/51.28                ( ( k2_tops_1 @ A @ B ) =
% 51.08/51.28                  ( k7_subset_1 @
% 51.08/51.28                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 51.08/51.28    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 51.08/51.28  thf('0', plain,
% 51.08/51.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf(t74_tops_1, axiom,
% 51.08/51.28    (![A:$i]:
% 51.08/51.28     ( ( l1_pre_topc @ A ) =>
% 51.08/51.28       ( ![B:$i]:
% 51.08/51.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.08/51.28           ( ( k1_tops_1 @ A @ B ) =
% 51.08/51.28             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 51.08/51.28  thf('1', plain,
% 51.08/51.28      (![X58 : $i, X59 : $i]:
% 51.08/51.28         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 51.08/51.28          | ((k1_tops_1 @ X59 @ X58)
% 51.08/51.28              = (k7_subset_1 @ (u1_struct_0 @ X59) @ X58 @ 
% 51.08/51.28                 (k2_tops_1 @ X59 @ X58)))
% 51.08/51.28          | ~ (l1_pre_topc @ X59))),
% 51.08/51.28      inference('cnf', [status(esa)], [t74_tops_1])).
% 51.08/51.28  thf('2', plain,
% 51.08/51.28      ((~ (l1_pre_topc @ sk_A)
% 51.08/51.28        | ((k1_tops_1 @ sk_A @ sk_B)
% 51.08/51.28            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 51.08/51.28               (k2_tops_1 @ sk_A @ sk_B))))),
% 51.08/51.28      inference('sup-', [status(thm)], ['0', '1'])).
% 51.08/51.28  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('4', plain,
% 51.08/51.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf(redefinition_k7_subset_1, axiom,
% 51.08/51.28    (![A:$i,B:$i,C:$i]:
% 51.08/51.28     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 51.08/51.28       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 51.08/51.28  thf('5', plain,
% 51.08/51.28      (![X38 : $i, X39 : $i, X40 : $i]:
% 51.08/51.28         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 51.08/51.28          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k4_xboole_0 @ X38 @ X40)))),
% 51.08/51.28      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 51.08/51.28  thf('6', plain,
% 51.08/51.28      (![X0 : $i]:
% 51.08/51.28         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 51.08/51.28           = (k4_xboole_0 @ sk_B @ X0))),
% 51.08/51.28      inference('sup-', [status(thm)], ['4', '5'])).
% 51.08/51.28  thf('7', plain,
% 51.08/51.28      (((k1_tops_1 @ sk_A @ sk_B)
% 51.08/51.28         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 51.08/51.28      inference('demod', [status(thm)], ['2', '3', '6'])).
% 51.08/51.28  thf('8', plain,
% 51.08/51.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 51.08/51.28        | (v3_pre_topc @ sk_B @ sk_A))),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('9', plain,
% 51.08/51.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 51.08/51.28         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 51.08/51.28      inference('split', [status(esa)], ['8'])).
% 51.08/51.28  thf('10', plain,
% 51.08/51.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 51.08/51.28        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('11', plain,
% 51.08/51.28      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 51.08/51.28       ~
% 51.08/51.28       (((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 51.08/51.28      inference('split', [status(esa)], ['10'])).
% 51.08/51.28  thf('12', plain,
% 51.08/51.28      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 51.08/51.28      inference('split', [status(esa)], ['8'])).
% 51.08/51.28  thf('13', plain,
% 51.08/51.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf(t55_tops_1, axiom,
% 51.08/51.28    (![A:$i]:
% 51.08/51.28     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 51.08/51.28       ( ![B:$i]:
% 51.08/51.28         ( ( l1_pre_topc @ B ) =>
% 51.08/51.28           ( ![C:$i]:
% 51.08/51.28             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.08/51.28               ( ![D:$i]:
% 51.08/51.28                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 51.08/51.28                   ( ( ( v3_pre_topc @ D @ B ) =>
% 51.08/51.28                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 51.08/51.28                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 51.08/51.28                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 51.08/51.28  thf('14', plain,
% 51.08/51.28      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 51.08/51.28         (~ (l1_pre_topc @ X50)
% 51.08/51.28          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 51.08/51.28          | ~ (v3_pre_topc @ X51 @ X50)
% 51.08/51.28          | ((k1_tops_1 @ X50 @ X51) = (X51))
% 51.08/51.28          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 51.08/51.28          | ~ (l1_pre_topc @ X53)
% 51.08/51.28          | ~ (v2_pre_topc @ X53))),
% 51.08/51.28      inference('cnf', [status(esa)], [t55_tops_1])).
% 51.08/51.28  thf('15', plain,
% 51.08/51.28      ((![X50 : $i, X51 : $i]:
% 51.08/51.28          (~ (l1_pre_topc @ X50)
% 51.08/51.28           | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 51.08/51.28           | ~ (v3_pre_topc @ X51 @ X50)
% 51.08/51.28           | ((k1_tops_1 @ X50 @ X51) = (X51))))
% 51.08/51.28         <= ((![X50 : $i, X51 : $i]:
% 51.08/51.28                (~ (l1_pre_topc @ X50)
% 51.08/51.28                 | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 51.08/51.28                 | ~ (v3_pre_topc @ X51 @ X50)
% 51.08/51.28                 | ((k1_tops_1 @ X50 @ X51) = (X51)))))),
% 51.08/51.28      inference('split', [status(esa)], ['14'])).
% 51.08/51.28  thf('16', plain,
% 51.08/51.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('17', plain,
% 51.08/51.28      ((![X52 : $i, X53 : $i]:
% 51.08/51.28          (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 51.08/51.28           | ~ (l1_pre_topc @ X53)
% 51.08/51.28           | ~ (v2_pre_topc @ X53)))
% 51.08/51.28         <= ((![X52 : $i, X53 : $i]:
% 51.08/51.28                (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 51.08/51.28                 | ~ (l1_pre_topc @ X53)
% 51.08/51.28                 | ~ (v2_pre_topc @ X53))))),
% 51.08/51.28      inference('split', [status(esa)], ['14'])).
% 51.08/51.28  thf('18', plain,
% 51.08/51.28      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 51.08/51.28         <= ((![X52 : $i, X53 : $i]:
% 51.08/51.28                (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 51.08/51.28                 | ~ (l1_pre_topc @ X53)
% 51.08/51.28                 | ~ (v2_pre_topc @ X53))))),
% 51.08/51.28      inference('sup-', [status(thm)], ['16', '17'])).
% 51.08/51.28  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('21', plain,
% 51.08/51.28      (~
% 51.08/51.28       (![X52 : $i, X53 : $i]:
% 51.08/51.28          (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 51.08/51.28           | ~ (l1_pre_topc @ X53)
% 51.08/51.28           | ~ (v2_pre_topc @ X53)))),
% 51.08/51.28      inference('demod', [status(thm)], ['18', '19', '20'])).
% 51.08/51.28  thf('22', plain,
% 51.08/51.28      ((![X50 : $i, X51 : $i]:
% 51.08/51.28          (~ (l1_pre_topc @ X50)
% 51.08/51.28           | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 51.08/51.28           | ~ (v3_pre_topc @ X51 @ X50)
% 51.08/51.28           | ((k1_tops_1 @ X50 @ X51) = (X51)))) | 
% 51.08/51.28       (![X52 : $i, X53 : $i]:
% 51.08/51.28          (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 51.08/51.28           | ~ (l1_pre_topc @ X53)
% 51.08/51.28           | ~ (v2_pre_topc @ X53)))),
% 51.08/51.28      inference('split', [status(esa)], ['14'])).
% 51.08/51.28  thf('23', plain,
% 51.08/51.28      ((![X50 : $i, X51 : $i]:
% 51.08/51.28          (~ (l1_pre_topc @ X50)
% 51.08/51.28           | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 51.08/51.28           | ~ (v3_pre_topc @ X51 @ X50)
% 51.08/51.28           | ((k1_tops_1 @ X50 @ X51) = (X51))))),
% 51.08/51.28      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 51.08/51.28  thf('24', plain,
% 51.08/51.28      (![X50 : $i, X51 : $i]:
% 51.08/51.28         (~ (l1_pre_topc @ X50)
% 51.08/51.28          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 51.08/51.28          | ~ (v3_pre_topc @ X51 @ X50)
% 51.08/51.28          | ((k1_tops_1 @ X50 @ X51) = (X51)))),
% 51.08/51.28      inference('simpl_trail', [status(thm)], ['15', '23'])).
% 51.08/51.28  thf('25', plain,
% 51.08/51.28      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 51.08/51.28        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 51.08/51.28        | ~ (l1_pre_topc @ sk_A))),
% 51.08/51.28      inference('sup-', [status(thm)], ['13', '24'])).
% 51.08/51.28  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('27', plain,
% 51.08/51.28      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 51.08/51.28      inference('demod', [status(thm)], ['25', '26'])).
% 51.08/51.28  thf('28', plain,
% 51.08/51.28      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 51.08/51.28         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 51.08/51.28      inference('sup-', [status(thm)], ['12', '27'])).
% 51.08/51.28  thf('29', plain,
% 51.08/51.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf(l78_tops_1, axiom,
% 51.08/51.28    (![A:$i]:
% 51.08/51.28     ( ( l1_pre_topc @ A ) =>
% 51.08/51.28       ( ![B:$i]:
% 51.08/51.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.08/51.28           ( ( k2_tops_1 @ A @ B ) =
% 51.08/51.28             ( k7_subset_1 @
% 51.08/51.28               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 51.08/51.28               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 51.08/51.28  thf('30', plain,
% 51.08/51.28      (![X48 : $i, X49 : $i]:
% 51.08/51.28         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 51.08/51.28          | ((k2_tops_1 @ X49 @ X48)
% 51.08/51.28              = (k7_subset_1 @ (u1_struct_0 @ X49) @ 
% 51.08/51.28                 (k2_pre_topc @ X49 @ X48) @ (k1_tops_1 @ X49 @ X48)))
% 51.08/51.28          | ~ (l1_pre_topc @ X49))),
% 51.08/51.28      inference('cnf', [status(esa)], [l78_tops_1])).
% 51.08/51.28  thf('31', plain,
% 51.08/51.28      ((~ (l1_pre_topc @ sk_A)
% 51.08/51.28        | ((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 51.08/51.28      inference('sup-', [status(thm)], ['29', '30'])).
% 51.08/51.28  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('33', plain,
% 51.08/51.28      (((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 51.08/51.28            (k1_tops_1 @ sk_A @ sk_B)))),
% 51.08/51.28      inference('demod', [status(thm)], ['31', '32'])).
% 51.08/51.28  thf('34', plain,
% 51.08/51.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 51.08/51.28         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 51.08/51.28      inference('sup+', [status(thm)], ['28', '33'])).
% 51.08/51.28  thf('35', plain,
% 51.08/51.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 51.08/51.28         <= (~
% 51.08/51.28             (((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 51.08/51.28      inference('split', [status(esa)], ['10'])).
% 51.08/51.28  thf('36', plain,
% 51.08/51.28      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 51.08/51.28         <= (~
% 51.08/51.28             (((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 51.08/51.28             ((v3_pre_topc @ sk_B @ sk_A)))),
% 51.08/51.28      inference('sup-', [status(thm)], ['34', '35'])).
% 51.08/51.28  thf('37', plain,
% 51.08/51.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 51.08/51.28       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 51.08/51.28      inference('simplify', [status(thm)], ['36'])).
% 51.08/51.28  thf('38', plain,
% 51.08/51.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 51.08/51.28       ((v3_pre_topc @ sk_B @ sk_A))),
% 51.08/51.28      inference('split', [status(esa)], ['8'])).
% 51.08/51.28  thf('39', plain,
% 51.08/51.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 51.08/51.28      inference('sat_resolution*', [status(thm)], ['11', '37', '38'])).
% 51.08/51.28  thf('40', plain,
% 51.08/51.28      (((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 51.08/51.28            sk_B))),
% 51.08/51.28      inference('simpl_trail', [status(thm)], ['9', '39'])).
% 51.08/51.28  thf('41', plain,
% 51.08/51.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf(dt_k2_tops_1, axiom,
% 51.08/51.28    (![A:$i,B:$i]:
% 51.08/51.28     ( ( ( l1_pre_topc @ A ) & 
% 51.08/51.28         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 51.08/51.28       ( m1_subset_1 @
% 51.08/51.28         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 51.08/51.28  thf('42', plain,
% 51.08/51.28      (![X46 : $i, X47 : $i]:
% 51.08/51.28         (~ (l1_pre_topc @ X46)
% 51.08/51.28          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 51.08/51.28          | (m1_subset_1 @ (k2_tops_1 @ X46 @ X47) @ 
% 51.08/51.28             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 51.08/51.28      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 51.08/51.28  thf('43', plain,
% 51.08/51.28      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 51.08/51.28         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.08/51.28        | ~ (l1_pre_topc @ sk_A))),
% 51.08/51.28      inference('sup-', [status(thm)], ['41', '42'])).
% 51.08/51.28  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('45', plain,
% 51.08/51.28      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 51.08/51.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('demod', [status(thm)], ['43', '44'])).
% 51.08/51.28  thf('46', plain,
% 51.08/51.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf(dt_k4_subset_1, axiom,
% 51.08/51.28    (![A:$i,B:$i,C:$i]:
% 51.08/51.28     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 51.08/51.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 51.08/51.28       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 51.08/51.28  thf('47', plain,
% 51.08/51.28      (![X30 : $i, X31 : $i, X32 : $i]:
% 51.08/51.28         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 51.08/51.28          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31))
% 51.08/51.28          | (m1_subset_1 @ (k4_subset_1 @ X31 @ X30 @ X32) @ 
% 51.08/51.28             (k1_zfmisc_1 @ X31)))),
% 51.08/51.28      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 51.08/51.28  thf('48', plain,
% 51.08/51.28      (![X0 : $i]:
% 51.08/51.28         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 51.08/51.28           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.08/51.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 51.08/51.28      inference('sup-', [status(thm)], ['46', '47'])).
% 51.08/51.28  thf('49', plain,
% 51.08/51.28      ((m1_subset_1 @ 
% 51.08/51.28        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 51.08/51.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('sup-', [status(thm)], ['45', '48'])).
% 51.08/51.28  thf('50', plain,
% 51.08/51.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf(t65_tops_1, axiom,
% 51.08/51.28    (![A:$i]:
% 51.08/51.28     ( ( l1_pre_topc @ A ) =>
% 51.08/51.28       ( ![B:$i]:
% 51.08/51.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.08/51.28           ( ( k2_pre_topc @ A @ B ) =
% 51.08/51.28             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 51.08/51.28  thf('51', plain,
% 51.08/51.28      (![X56 : $i, X57 : $i]:
% 51.08/51.28         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 51.08/51.28          | ((k2_pre_topc @ X57 @ X56)
% 51.08/51.28              = (k4_subset_1 @ (u1_struct_0 @ X57) @ X56 @ 
% 51.08/51.28                 (k2_tops_1 @ X57 @ X56)))
% 51.08/51.28          | ~ (l1_pre_topc @ X57))),
% 51.08/51.28      inference('cnf', [status(esa)], [t65_tops_1])).
% 51.08/51.28  thf('52', plain,
% 51.08/51.28      ((~ (l1_pre_topc @ sk_A)
% 51.08/51.28        | ((k2_pre_topc @ sk_A @ sk_B)
% 51.08/51.28            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 51.08/51.28               (k2_tops_1 @ sk_A @ sk_B))))),
% 51.08/51.28      inference('sup-', [status(thm)], ['50', '51'])).
% 51.08/51.28  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('54', plain,
% 51.08/51.28      (((k2_pre_topc @ sk_A @ sk_B)
% 51.08/51.28         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 51.08/51.28            (k2_tops_1 @ sk_A @ sk_B)))),
% 51.08/51.28      inference('demod', [status(thm)], ['52', '53'])).
% 51.08/51.28  thf('55', plain,
% 51.08/51.28      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 51.08/51.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('demod', [status(thm)], ['49', '54'])).
% 51.08/51.28  thf('56', plain,
% 51.08/51.28      (![X38 : $i, X39 : $i, X40 : $i]:
% 51.08/51.28         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 51.08/51.28          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k4_xboole_0 @ X38 @ X40)))),
% 51.08/51.28      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 51.08/51.28  thf('57', plain,
% 51.08/51.28      (![X0 : $i]:
% 51.08/51.28         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 51.08/51.28           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 51.08/51.28      inference('sup-', [status(thm)], ['55', '56'])).
% 51.08/51.28  thf('58', plain,
% 51.08/51.28      (((k2_tops_1 @ sk_A @ sk_B)
% 51.08/51.28         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 51.08/51.28      inference('demod', [status(thm)], ['40', '57'])).
% 51.08/51.28  thf(idempotence_k3_xboole_0, axiom,
% 51.08/51.28    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 51.08/51.28  thf('59', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 51.08/51.28      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 51.08/51.28  thf(t12_setfam_1, axiom,
% 51.08/51.28    (![A:$i,B:$i]:
% 51.08/51.28     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 51.08/51.28  thf('60', plain,
% 51.08/51.28      (![X41 : $i, X42 : $i]:
% 51.08/51.28         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 51.08/51.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 51.08/51.28  thf('61', plain,
% 51.08/51.28      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 51.08/51.28      inference('demod', [status(thm)], ['59', '60'])).
% 51.08/51.28  thf(t16_xboole_1, axiom,
% 51.08/51.28    (![A:$i,B:$i,C:$i]:
% 51.08/51.28     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 51.08/51.28       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 51.08/51.28  thf('62', plain,
% 51.08/51.28      (![X6 : $i, X7 : $i, X8 : $i]:
% 51.08/51.28         ((k3_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8)
% 51.08/51.28           = (k3_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 51.08/51.28      inference('cnf', [status(esa)], [t16_xboole_1])).
% 51.08/51.28  thf('63', plain,
% 51.08/51.28      (![X41 : $i, X42 : $i]:
% 51.08/51.28         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 51.08/51.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 51.08/51.28  thf('64', plain,
% 51.08/51.28      (![X41 : $i, X42 : $i]:
% 51.08/51.28         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 51.08/51.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 51.08/51.28  thf('65', plain,
% 51.08/51.28      (![X41 : $i, X42 : $i]:
% 51.08/51.28         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 51.08/51.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 51.08/51.28  thf('66', plain,
% 51.08/51.28      (![X41 : $i, X42 : $i]:
% 51.08/51.28         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 51.08/51.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 51.08/51.28  thf('67', plain,
% 51.08/51.28      (![X6 : $i, X7 : $i, X8 : $i]:
% 51.08/51.28         ((k1_setfam_1 @ 
% 51.08/51.28           (k2_tarski @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7)) @ X8))
% 51.08/51.28           = (k1_setfam_1 @ 
% 51.08/51.28              (k2_tarski @ X6 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8)))))),
% 51.08/51.28      inference('demod', [status(thm)], ['62', '63', '64', '65', '66'])).
% 51.08/51.28  thf('68', plain,
% 51.08/51.28      (![X0 : $i, X1 : $i]:
% 51.08/51.28         ((k1_setfam_1 @ (k2_tarski @ X0 @ X1))
% 51.08/51.28           = (k1_setfam_1 @ 
% 51.08/51.28              (k2_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))))),
% 51.08/51.28      inference('sup+', [status(thm)], ['61', '67'])).
% 51.08/51.28  thf(commutativity_k2_tarski, axiom,
% 51.08/51.28    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 51.08/51.28  thf('69', plain,
% 51.08/51.28      (![X24 : $i, X25 : $i]:
% 51.08/51.28         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 51.08/51.28      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 51.08/51.28  thf(t100_xboole_1, axiom,
% 51.08/51.28    (![A:$i,B:$i]:
% 51.08/51.28     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 51.08/51.28  thf('70', plain,
% 51.08/51.28      (![X4 : $i, X5 : $i]:
% 51.08/51.28         ((k4_xboole_0 @ X4 @ X5)
% 51.08/51.28           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 51.08/51.28      inference('cnf', [status(esa)], [t100_xboole_1])).
% 51.08/51.28  thf('71', plain,
% 51.08/51.28      (![X41 : $i, X42 : $i]:
% 51.08/51.28         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 51.08/51.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 51.08/51.28  thf('72', plain,
% 51.08/51.28      (![X4 : $i, X5 : $i]:
% 51.08/51.28         ((k4_xboole_0 @ X4 @ X5)
% 51.08/51.28           = (k5_xboole_0 @ X4 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 51.08/51.28      inference('demod', [status(thm)], ['70', '71'])).
% 51.08/51.28  thf('73', plain,
% 51.08/51.28      (![X0 : $i, X1 : $i]:
% 51.08/51.28         ((k4_xboole_0 @ X0 @ X1)
% 51.08/51.28           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 51.08/51.28      inference('sup+', [status(thm)], ['69', '72'])).
% 51.08/51.28  thf('74', plain,
% 51.08/51.28      (![X0 : $i, X1 : $i]:
% 51.08/51.28         ((k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X1)
% 51.08/51.28           = (k5_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 51.08/51.28              (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 51.08/51.28      inference('sup+', [status(thm)], ['68', '73'])).
% 51.08/51.28  thf(t3_boole, axiom,
% 51.08/51.28    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 51.08/51.28  thf('75', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 51.08/51.28      inference('cnf', [status(esa)], [t3_boole])).
% 51.08/51.28  thf(t36_xboole_1, axiom,
% 51.08/51.28    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 51.08/51.28  thf('76', plain,
% 51.08/51.28      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 51.08/51.28      inference('cnf', [status(esa)], [t36_xboole_1])).
% 51.08/51.28  thf('77', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 51.08/51.28      inference('sup+', [status(thm)], ['75', '76'])).
% 51.08/51.28  thf(l32_xboole_1, axiom,
% 51.08/51.28    (![A:$i,B:$i]:
% 51.08/51.28     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 51.08/51.28  thf('78', plain,
% 51.08/51.28      (![X1 : $i, X3 : $i]:
% 51.08/51.28         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 51.08/51.28      inference('cnf', [status(esa)], [l32_xboole_1])).
% 51.08/51.28  thf('79', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 51.08/51.28      inference('sup-', [status(thm)], ['77', '78'])).
% 51.08/51.28  thf('80', plain,
% 51.08/51.28      (![X4 : $i, X5 : $i]:
% 51.08/51.28         ((k4_xboole_0 @ X4 @ X5)
% 51.08/51.28           = (k5_xboole_0 @ X4 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 51.08/51.28      inference('demod', [status(thm)], ['70', '71'])).
% 51.08/51.28  thf('81', plain,
% 51.08/51.28      (![X0 : $i]:
% 51.08/51.28         ((k1_xboole_0)
% 51.08/51.28           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X0))))),
% 51.08/51.28      inference('sup+', [status(thm)], ['79', '80'])).
% 51.08/51.28  thf('82', plain,
% 51.08/51.28      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 51.08/51.28      inference('demod', [status(thm)], ['59', '60'])).
% 51.08/51.28  thf('83', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 51.08/51.28      inference('demod', [status(thm)], ['81', '82'])).
% 51.08/51.28  thf('84', plain,
% 51.08/51.28      (![X0 : $i, X1 : $i]:
% 51.08/51.28         ((k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X1)
% 51.08/51.28           = (k1_xboole_0))),
% 51.08/51.28      inference('demod', [status(thm)], ['74', '83'])).
% 51.08/51.28  thf(t49_xboole_1, axiom,
% 51.08/51.28    (![A:$i,B:$i,C:$i]:
% 51.08/51.28     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 51.08/51.28       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 51.08/51.28  thf('85', plain,
% 51.08/51.28      (![X18 : $i, X19 : $i, X20 : $i]:
% 51.08/51.28         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 51.08/51.28           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 51.08/51.28      inference('cnf', [status(esa)], [t49_xboole_1])).
% 51.08/51.28  thf('86', plain,
% 51.08/51.28      (![X41 : $i, X42 : $i]:
% 51.08/51.28         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 51.08/51.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 51.08/51.28  thf('87', plain,
% 51.08/51.28      (![X41 : $i, X42 : $i]:
% 51.08/51.28         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 51.08/51.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 51.08/51.28  thf('88', plain,
% 51.08/51.28      (![X18 : $i, X19 : $i, X20 : $i]:
% 51.08/51.28         ((k1_setfam_1 @ (k2_tarski @ X18 @ (k4_xboole_0 @ X19 @ X20)))
% 51.08/51.28           = (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X18 @ X19)) @ X20))),
% 51.08/51.28      inference('demod', [status(thm)], ['85', '86', '87'])).
% 51.08/51.28  thf('89', plain,
% 51.08/51.28      (![X4 : $i, X5 : $i]:
% 51.08/51.28         ((k4_xboole_0 @ X4 @ X5)
% 51.08/51.28           = (k5_xboole_0 @ X4 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 51.08/51.28      inference('demod', [status(thm)], ['70', '71'])).
% 51.08/51.28  thf('90', plain,
% 51.08/51.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.08/51.28         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 51.08/51.28           = (k5_xboole_0 @ X2 @ 
% 51.08/51.28              (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X1)) @ X0)))),
% 51.08/51.28      inference('sup+', [status(thm)], ['88', '89'])).
% 51.08/51.28  thf('91', plain,
% 51.08/51.28      (![X0 : $i, X1 : $i]:
% 51.08/51.28         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 51.08/51.28           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 51.08/51.28      inference('sup+', [status(thm)], ['84', '90'])).
% 51.08/51.28  thf('92', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 51.08/51.28      inference('cnf', [status(esa)], [t3_boole])).
% 51.08/51.28  thf('93', plain,
% 51.08/51.28      (![X4 : $i, X5 : $i]:
% 51.08/51.28         ((k4_xboole_0 @ X4 @ X5)
% 51.08/51.28           = (k5_xboole_0 @ X4 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 51.08/51.28      inference('demod', [status(thm)], ['70', '71'])).
% 51.08/51.28  thf('94', plain,
% 51.08/51.28      (![X0 : $i]:
% 51.08/51.28         ((X0)
% 51.08/51.28           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0))))),
% 51.08/51.28      inference('sup+', [status(thm)], ['92', '93'])).
% 51.08/51.28  thf(t2_boole, axiom,
% 51.08/51.28    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 51.08/51.28  thf('95', plain,
% 51.08/51.28      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 51.08/51.28      inference('cnf', [status(esa)], [t2_boole])).
% 51.08/51.28  thf('96', plain,
% 51.08/51.28      (![X41 : $i, X42 : $i]:
% 51.08/51.28         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 51.08/51.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 51.08/51.28  thf('97', plain,
% 51.08/51.28      (![X11 : $i]:
% 51.08/51.28         ((k1_setfam_1 @ (k2_tarski @ X11 @ k1_xboole_0)) = (k1_xboole_0))),
% 51.08/51.28      inference('demod', [status(thm)], ['95', '96'])).
% 51.08/51.28  thf('98', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 51.08/51.28      inference('demod', [status(thm)], ['94', '97'])).
% 51.08/51.28  thf('99', plain,
% 51.08/51.28      (![X0 : $i, X1 : $i]:
% 51.08/51.28         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 51.08/51.28      inference('demod', [status(thm)], ['91', '98'])).
% 51.08/51.28  thf('100', plain,
% 51.08/51.28      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 51.08/51.28      inference('sup+', [status(thm)], ['58', '99'])).
% 51.08/51.28  thf('101', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 51.08/51.28      inference('sup+', [status(thm)], ['7', '100'])).
% 51.08/51.28  thf('102', plain,
% 51.08/51.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf(t3_subset, axiom,
% 51.08/51.28    (![A:$i,B:$i]:
% 51.08/51.28     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 51.08/51.28  thf('103', plain,
% 51.08/51.28      (![X43 : $i, X44 : $i]:
% 51.08/51.28         ((r1_tarski @ X43 @ X44) | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 51.08/51.28      inference('cnf', [status(esa)], [t3_subset])).
% 51.08/51.28  thf('104', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 51.08/51.28      inference('sup-', [status(thm)], ['102', '103'])).
% 51.08/51.28  thf(t28_xboole_1, axiom,
% 51.08/51.28    (![A:$i,B:$i]:
% 51.08/51.28     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 51.08/51.28  thf('105', plain,
% 51.08/51.28      (![X9 : $i, X10 : $i]:
% 51.08/51.28         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 51.08/51.28      inference('cnf', [status(esa)], [t28_xboole_1])).
% 51.08/51.28  thf('106', plain,
% 51.08/51.28      (![X41 : $i, X42 : $i]:
% 51.08/51.28         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 51.08/51.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 51.08/51.28  thf('107', plain,
% 51.08/51.28      (![X9 : $i, X10 : $i]:
% 51.08/51.28         (((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (X9))
% 51.08/51.28          | ~ (r1_tarski @ X9 @ X10))),
% 51.08/51.28      inference('demod', [status(thm)], ['105', '106'])).
% 51.08/51.28  thf('108', plain,
% 51.08/51.28      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 51.08/51.28      inference('sup-', [status(thm)], ['104', '107'])).
% 51.08/51.28  thf('109', plain,
% 51.08/51.28      (![X0 : $i, X1 : $i]:
% 51.08/51.28         ((k4_xboole_0 @ X0 @ X1)
% 51.08/51.28           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 51.08/51.28      inference('sup+', [status(thm)], ['69', '72'])).
% 51.08/51.28  thf('110', plain,
% 51.08/51.28      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 51.08/51.28         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 51.08/51.28      inference('sup+', [status(thm)], ['108', '109'])).
% 51.08/51.28  thf('111', plain,
% 51.08/51.28      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 51.08/51.28      inference('cnf', [status(esa)], [t36_xboole_1])).
% 51.08/51.28  thf('112', plain,
% 51.08/51.28      (![X43 : $i, X45 : $i]:
% 51.08/51.28         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X45)) | ~ (r1_tarski @ X43 @ X45))),
% 51.08/51.28      inference('cnf', [status(esa)], [t3_subset])).
% 51.08/51.28  thf('113', plain,
% 51.08/51.28      (![X0 : $i, X1 : $i]:
% 51.08/51.28         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 51.08/51.28      inference('sup-', [status(thm)], ['111', '112'])).
% 51.08/51.28  thf(d5_subset_1, axiom,
% 51.08/51.28    (![A:$i,B:$i]:
% 51.08/51.28     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 51.08/51.28       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 51.08/51.28  thf('114', plain,
% 51.08/51.28      (![X26 : $i, X27 : $i]:
% 51.08/51.28         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 51.08/51.28          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 51.08/51.28      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.08/51.28  thf('115', plain,
% 51.08/51.28      (![X0 : $i, X1 : $i]:
% 51.08/51.28         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 51.08/51.28           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 51.08/51.28      inference('sup-', [status(thm)], ['113', '114'])).
% 51.08/51.28  thf('116', plain,
% 51.08/51.28      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 51.08/51.28         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 51.08/51.28      inference('sup+', [status(thm)], ['110', '115'])).
% 51.08/51.28  thf('117', plain,
% 51.08/51.28      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 51.08/51.28         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 51.08/51.28      inference('sup+', [status(thm)], ['108', '109'])).
% 51.08/51.28  thf('118', plain,
% 51.08/51.28      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 51.08/51.28         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 51.08/51.28      inference('demod', [status(thm)], ['116', '117'])).
% 51.08/51.28  thf('119', plain,
% 51.08/51.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf(involutiveness_k3_subset_1, axiom,
% 51.08/51.28    (![A:$i,B:$i]:
% 51.08/51.28     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 51.08/51.28       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 51.08/51.28  thf('120', plain,
% 51.08/51.28      (![X33 : $i, X34 : $i]:
% 51.08/51.28         (((k3_subset_1 @ X34 @ (k3_subset_1 @ X34 @ X33)) = (X33))
% 51.08/51.28          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 51.08/51.28      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 51.08/51.28  thf('121', plain,
% 51.08/51.28      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 51.08/51.28      inference('sup-', [status(thm)], ['119', '120'])).
% 51.08/51.28  thf('122', plain,
% 51.08/51.28      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 51.08/51.28         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 51.08/51.28      inference('sup+', [status(thm)], ['108', '109'])).
% 51.08/51.28  thf('123', plain,
% 51.08/51.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('124', plain,
% 51.08/51.28      (![X26 : $i, X27 : $i]:
% 51.08/51.28         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 51.08/51.28          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 51.08/51.28      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.08/51.28  thf('125', plain,
% 51.08/51.28      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 51.08/51.28         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 51.08/51.28      inference('sup-', [status(thm)], ['123', '124'])).
% 51.08/51.28  thf('126', plain,
% 51.08/51.28      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 51.08/51.28         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 51.08/51.28      inference('sup+', [status(thm)], ['122', '125'])).
% 51.08/51.28  thf('127', plain,
% 51.08/51.28      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 51.08/51.28      inference('demod', [status(thm)], ['121', '126'])).
% 51.08/51.28  thf('128', plain,
% 51.08/51.28      (((sk_B)
% 51.08/51.28         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 51.08/51.28      inference('demod', [status(thm)], ['118', '127'])).
% 51.08/51.28  thf('129', plain,
% 51.08/51.28      (![X0 : $i, X1 : $i]:
% 51.08/51.28         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 51.08/51.28      inference('sup-', [status(thm)], ['111', '112'])).
% 51.08/51.28  thf('130', plain,
% 51.08/51.28      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 51.08/51.28         (~ (l1_pre_topc @ X50)
% 51.08/51.28          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 51.08/51.28          | ((k1_tops_1 @ X53 @ X52) != (X52))
% 51.08/51.28          | (v3_pre_topc @ X52 @ X53)
% 51.08/51.28          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 51.08/51.28          | ~ (l1_pre_topc @ X53)
% 51.08/51.28          | ~ (v2_pre_topc @ X53))),
% 51.08/51.28      inference('cnf', [status(esa)], [t55_tops_1])).
% 51.08/51.28  thf('131', plain,
% 51.08/51.28      ((![X52 : $i, X53 : $i]:
% 51.08/51.28          (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 51.08/51.28           | ~ (l1_pre_topc @ X53)
% 51.08/51.28           | ~ (v2_pre_topc @ X53)
% 51.08/51.28           | ((k1_tops_1 @ X53 @ X52) != (X52))
% 51.08/51.28           | (v3_pre_topc @ X52 @ X53)))
% 51.08/51.28         <= ((![X52 : $i, X53 : $i]:
% 51.08/51.28                (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 51.08/51.28                 | ~ (l1_pre_topc @ X53)
% 51.08/51.28                 | ~ (v2_pre_topc @ X53)
% 51.08/51.28                 | ((k1_tops_1 @ X53 @ X52) != (X52))
% 51.08/51.28                 | (v3_pre_topc @ X52 @ X53))))),
% 51.08/51.28      inference('split', [status(esa)], ['130'])).
% 51.08/51.28  thf('132', plain,
% 51.08/51.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('133', plain,
% 51.08/51.28      ((![X50 : $i, X51 : $i]:
% 51.08/51.28          (~ (l1_pre_topc @ X50)
% 51.08/51.28           | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))))
% 51.08/51.28         <= ((![X50 : $i, X51 : $i]:
% 51.08/51.28                (~ (l1_pre_topc @ X50)
% 51.08/51.28                 | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50))))))),
% 51.08/51.28      inference('split', [status(esa)], ['130'])).
% 51.08/51.28  thf('134', plain,
% 51.08/51.28      ((~ (l1_pre_topc @ sk_A))
% 51.08/51.28         <= ((![X50 : $i, X51 : $i]:
% 51.08/51.28                (~ (l1_pre_topc @ X50)
% 51.08/51.28                 | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50))))))),
% 51.08/51.28      inference('sup-', [status(thm)], ['132', '133'])).
% 51.08/51.28  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('136', plain,
% 51.08/51.28      (~
% 51.08/51.28       (![X50 : $i, X51 : $i]:
% 51.08/51.28          (~ (l1_pre_topc @ X50)
% 51.08/51.28           | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))))),
% 51.08/51.28      inference('demod', [status(thm)], ['134', '135'])).
% 51.08/51.28  thf('137', plain,
% 51.08/51.28      ((![X52 : $i, X53 : $i]:
% 51.08/51.28          (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 51.08/51.28           | ~ (l1_pre_topc @ X53)
% 51.08/51.28           | ~ (v2_pre_topc @ X53)
% 51.08/51.28           | ((k1_tops_1 @ X53 @ X52) != (X52))
% 51.08/51.28           | (v3_pre_topc @ X52 @ X53))) | 
% 51.08/51.28       (![X50 : $i, X51 : $i]:
% 51.08/51.28          (~ (l1_pre_topc @ X50)
% 51.08/51.28           | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))))),
% 51.08/51.28      inference('split', [status(esa)], ['130'])).
% 51.08/51.28  thf('138', plain,
% 51.08/51.28      ((![X52 : $i, X53 : $i]:
% 51.08/51.28          (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 51.08/51.28           | ~ (l1_pre_topc @ X53)
% 51.08/51.28           | ~ (v2_pre_topc @ X53)
% 51.08/51.28           | ((k1_tops_1 @ X53 @ X52) != (X52))
% 51.08/51.28           | (v3_pre_topc @ X52 @ X53)))),
% 51.08/51.28      inference('sat_resolution*', [status(thm)], ['136', '137'])).
% 51.08/51.28  thf('139', plain,
% 51.08/51.28      (![X52 : $i, X53 : $i]:
% 51.08/51.28         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 51.08/51.28          | ~ (l1_pre_topc @ X53)
% 51.08/51.28          | ~ (v2_pre_topc @ X53)
% 51.08/51.28          | ((k1_tops_1 @ X53 @ X52) != (X52))
% 51.08/51.28          | (v3_pre_topc @ X52 @ X53))),
% 51.08/51.28      inference('simpl_trail', [status(thm)], ['131', '138'])).
% 51.08/51.28  thf('140', plain,
% 51.08/51.28      (![X0 : $i, X1 : $i]:
% 51.08/51.28         ((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 51.08/51.28          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 51.08/51.28              != (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 51.08/51.28          | ~ (v2_pre_topc @ X0)
% 51.08/51.28          | ~ (l1_pre_topc @ X0))),
% 51.08/51.28      inference('sup-', [status(thm)], ['129', '139'])).
% 51.08/51.28  thf('141', plain,
% 51.08/51.28      ((((k1_tops_1 @ sk_A @ sk_B)
% 51.08/51.28          != (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28              (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 51.08/51.28        | ~ (l1_pre_topc @ sk_A)
% 51.08/51.28        | ~ (v2_pre_topc @ sk_A)
% 51.08/51.28        | (v3_pre_topc @ 
% 51.08/51.28           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 51.08/51.28           sk_A))),
% 51.08/51.28      inference('sup-', [status(thm)], ['128', '140'])).
% 51.08/51.28  thf('142', plain,
% 51.08/51.28      (((sk_B)
% 51.08/51.28         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 51.08/51.28      inference('demod', [status(thm)], ['118', '127'])).
% 51.08/51.28  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('144', plain, ((v2_pre_topc @ sk_A)),
% 51.08/51.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.28  thf('145', plain,
% 51.08/51.28      (((sk_B)
% 51.08/51.28         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 51.08/51.28            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 51.08/51.28      inference('demod', [status(thm)], ['118', '127'])).
% 51.08/51.28  thf('146', plain,
% 51.08/51.28      ((((k1_tops_1 @ sk_A @ sk_B) != (sk_B)) | (v3_pre_topc @ sk_B @ sk_A))),
% 51.08/51.28      inference('demod', [status(thm)], ['141', '142', '143', '144', '145'])).
% 51.08/51.28  thf('147', plain,
% 51.08/51.28      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 51.08/51.28      inference('split', [status(esa)], ['10'])).
% 51.08/51.28  thf('148', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 51.08/51.28      inference('sat_resolution*', [status(thm)], ['11', '37'])).
% 51.08/51.28  thf('149', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 51.08/51.28      inference('simpl_trail', [status(thm)], ['147', '148'])).
% 51.08/51.28  thf('150', plain, (((k1_tops_1 @ sk_A @ sk_B) != (sk_B))),
% 51.08/51.28      inference('clc', [status(thm)], ['146', '149'])).
% 51.08/51.28  thf('151', plain, ($false),
% 51.08/51.28      inference('simplify_reflect-', [status(thm)], ['101', '150'])).
% 51.08/51.28  
% 51.08/51.28  % SZS output end Refutation
% 51.08/51.28  
% 51.08/51.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
