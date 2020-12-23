%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6l05DUbB7X

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:29 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 581 expanded)
%              Number of leaves         :   35 ( 180 expanded)
%              Depth                    :   18
%              Number of atoms          : 1708 (7703 expanded)
%              Number of equality atoms :  110 ( 415 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( v3_pre_topc @ X48 @ X47 )
      | ( ( k1_tops_1 @ X47 @ X48 )
        = X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('7',plain,
    ( ! [X47: $i,X48: $i] :
        ( ~ ( l1_pre_topc @ X47 )
        | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
        | ~ ( v3_pre_topc @ X48 @ X47 )
        | ( ( k1_tops_1 @ X47 @ X48 )
          = X48 ) )
   <= ! [X47: $i,X48: $i] :
        ( ~ ( l1_pre_topc @ X47 )
        | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
        | ~ ( v3_pre_topc @ X48 @ X47 )
        | ( ( k1_tops_1 @ X47 @ X48 )
          = X48 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X49: $i,X50: $i] :
        ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
        | ~ ( l1_pre_topc @ X50 )
        | ~ ( v2_pre_topc @ X50 ) )
   <= ! [X49: $i,X50: $i] :
        ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
        | ~ ( l1_pre_topc @ X50 )
        | ~ ( v2_pre_topc @ X50 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X49: $i,X50: $i] :
        ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
        | ~ ( l1_pre_topc @ X50 )
        | ~ ( v2_pre_topc @ X50 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ! [X49: $i,X50: $i] :
        ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
        | ~ ( l1_pre_topc @ X50 )
        | ~ ( v2_pre_topc @ X50 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ! [X47: $i,X48: $i] :
        ( ~ ( l1_pre_topc @ X47 )
        | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
        | ~ ( v3_pre_topc @ X48 @ X47 )
        | ( ( k1_tops_1 @ X47 @ X48 )
          = X48 ) )
    | ! [X49: $i,X50: $i] :
        ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
        | ~ ( l1_pre_topc @ X50 )
        | ~ ( v2_pre_topc @ X50 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( l1_pre_topc @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( v3_pre_topc @ X48 @ X47 )
      | ( ( k1_tops_1 @ X47 @ X48 )
        = X48 ) ) ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( l1_pre_topc @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( v3_pre_topc @ X48 @ X47 )
      | ( ( k1_tops_1 @ X47 @ X48 )
        = X48 ) ) ),
    inference(simpl_trail,[status(thm)],['7','15'])).

thf('17',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k2_tops_1 @ X46 @ X45 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X46 ) @ ( k2_pre_topc @ X46 @ X45 ) @ ( k1_tops_1 @ X46 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k6_subset_1 @ X26 @ X27 )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k6_subset_1 @ X28 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['20','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','41'])).

thf('43',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( ( k1_tops_1 @ X50 @ X49 )
       != X49 )
      | ( v3_pre_topc @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('46',plain,
    ( ! [X49: $i,X50: $i] :
        ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
        | ~ ( l1_pre_topc @ X50 )
        | ~ ( v2_pre_topc @ X50 )
        | ( ( k1_tops_1 @ X50 @ X49 )
         != X49 )
        | ( v3_pre_topc @ X49 @ X50 ) )
   <= ! [X49: $i,X50: $i] :
        ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
        | ~ ( l1_pre_topc @ X50 )
        | ~ ( v2_pre_topc @ X50 )
        | ( ( k1_tops_1 @ X50 @ X49 )
         != X49 )
        | ( v3_pre_topc @ X49 @ X50 ) ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ! [X47: $i,X48: $i] :
        ( ~ ( l1_pre_topc @ X47 )
        | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) ) )
   <= ! [X47: $i,X48: $i] :
        ( ~ ( l1_pre_topc @ X47 )
        | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) ) ) ),
    inference(split,[status(esa)],['45'])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X47: $i,X48: $i] :
        ( ~ ( l1_pre_topc @ X47 )
        | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ~ ! [X47: $i,X48: $i] :
        ( ~ ( l1_pre_topc @ X47 )
        | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X49: $i,X50: $i] :
        ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
        | ~ ( l1_pre_topc @ X50 )
        | ~ ( v2_pre_topc @ X50 )
        | ( ( k1_tops_1 @ X50 @ X49 )
         != X49 )
        | ( v3_pre_topc @ X49 @ X50 ) )
    | ! [X47: $i,X48: $i] :
        ( ~ ( l1_pre_topc @ X47 )
        | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) ) ) ),
    inference(split,[status(esa)],['45'])).

thf('53',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 )
      | ( ( k1_tops_1 @ X50 @ X49 )
       != X49 )
      | ( v3_pre_topc @ X49 @ X50 ) ) ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 )
      | ( ( k1_tops_1 @ X50 @ X49 )
       != X49 )
      | ( v3_pre_topc @ X49 @ X50 ) ) ),
    inference(simpl_trail,[status(thm)],['46','53'])).

thf('55',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('60',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( ( k1_tops_1 @ X54 @ X53 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X54 ) @ X53 @ ( k2_tops_1 @ X54 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k6_subset_1 @ X28 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('68',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k6_subset_1 @ X26 @ X27 )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('69',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k6_subset_1 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('73',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('75',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( l1_pre_topc @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('80',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k4_subset_1 @ X24 @ X23 @ X25 )
        = ( k2_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('84',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( ( k2_pre_topc @ X52 @ X51 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X52 ) @ X51 @ ( k2_tops_1 @ X52 @ X51 ) ) )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['73','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('91',plain,(
    ! [X16: $i,X17: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('92',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('94',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('95',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k6_subset_1 @ X26 @ X27 )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('96',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X36: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r1_tarski @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('100',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X22 @ ( k3_subset_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('106',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('107',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k6_subset_1 @ X26 @ X27 )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('108',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k6_subset_1 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['101','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['90','111'])).

thf('113',plain,(
    ! [X16: $i,X17: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('114',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k6_subset_1 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['112','115'])).

thf('117',plain,
    ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k6_subset_1 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['89','116'])).

thf('118',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['73','88'])).

thf('119',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','34'])).

thf('120',plain,
    ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('122',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('123',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['101','110'])).

thf('126',plain,
    ( ( k3_subset_1 @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('128',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('130',plain,
    ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,
    ( ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['123','130'])).

thf('132',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('133',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','41','132'])).

thf('134',plain,
    ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['131','133'])).

thf('135',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['120','134'])).

thf('136',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['58','135'])).

thf('137',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['43','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6l05DUbB7X
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:16:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.79/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/1.00  % Solved by: fo/fo7.sh
% 0.79/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/1.00  % done 856 iterations in 0.538s
% 0.79/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/1.00  % SZS output start Refutation
% 0.79/1.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.79/1.00  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.79/1.00  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.79/1.00  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.79/1.00  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.79/1.00  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.79/1.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.79/1.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.79/1.00  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.79/1.00  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.79/1.00  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.79/1.00  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.79/1.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.79/1.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.79/1.00  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.79/1.00  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.79/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.79/1.00  thf(t76_tops_1, conjecture,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.79/1.00       ( ![B:$i]:
% 0.79/1.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.79/1.00           ( ( v3_pre_topc @ B @ A ) <=>
% 0.79/1.00             ( ( k2_tops_1 @ A @ B ) =
% 0.79/1.00               ( k7_subset_1 @
% 0.79/1.00                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.79/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.79/1.00    (~( ![A:$i]:
% 0.79/1.00        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.79/1.00          ( ![B:$i]:
% 0.79/1.00            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.79/1.00              ( ( v3_pre_topc @ B @ A ) <=>
% 0.79/1.00                ( ( k2_tops_1 @ A @ B ) =
% 0.79/1.00                  ( k7_subset_1 @
% 0.79/1.00                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.79/1.00    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.79/1.00  thf('0', plain,
% 0.79/1.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.00          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.00              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.79/1.00        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf('1', plain,
% 0.79/1.00      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.79/1.00      inference('split', [status(esa)], ['0'])).
% 0.79/1.00  thf('2', plain,
% 0.79/1.00      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.79/1.00       ~
% 0.79/1.00       (((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.00          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.00             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.79/1.00      inference('split', [status(esa)], ['0'])).
% 0.79/1.00  thf('3', plain,
% 0.79/1.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.00          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.00             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.79/1.00        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf('4', plain,
% 0.79/1.00      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.79/1.00      inference('split', [status(esa)], ['3'])).
% 0.79/1.00  thf('5', plain,
% 0.79/1.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf(t55_tops_1, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.79/1.00       ( ![B:$i]:
% 0.79/1.00         ( ( l1_pre_topc @ B ) =>
% 0.79/1.00           ( ![C:$i]:
% 0.79/1.00             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.79/1.00               ( ![D:$i]:
% 0.79/1.00                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.79/1.00                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.79/1.00                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.79/1.00                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.79/1.00                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.79/1.00  thf('6', plain,
% 0.79/1.00      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.79/1.00         (~ (l1_pre_topc @ X47)
% 0.79/1.00          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.79/1.00          | ~ (v3_pre_topc @ X48 @ X47)
% 0.79/1.00          | ((k1_tops_1 @ X47 @ X48) = (X48))
% 0.79/1.00          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.79/1.00          | ~ (l1_pre_topc @ X50)
% 0.79/1.00          | ~ (v2_pre_topc @ X50))),
% 0.79/1.00      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.79/1.00  thf('7', plain,
% 0.79/1.00      ((![X47 : $i, X48 : $i]:
% 0.79/1.00          (~ (l1_pre_topc @ X47)
% 0.79/1.00           | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.79/1.00           | ~ (v3_pre_topc @ X48 @ X47)
% 0.79/1.00           | ((k1_tops_1 @ X47 @ X48) = (X48))))
% 0.79/1.00         <= ((![X47 : $i, X48 : $i]:
% 0.79/1.00                (~ (l1_pre_topc @ X47)
% 0.79/1.00                 | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.79/1.00                 | ~ (v3_pre_topc @ X48 @ X47)
% 0.79/1.00                 | ((k1_tops_1 @ X47 @ X48) = (X48)))))),
% 0.79/1.00      inference('split', [status(esa)], ['6'])).
% 0.79/1.00  thf('8', plain,
% 0.79/1.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf('9', plain,
% 0.79/1.00      ((![X49 : $i, X50 : $i]:
% 0.79/1.00          (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.79/1.00           | ~ (l1_pre_topc @ X50)
% 0.79/1.00           | ~ (v2_pre_topc @ X50)))
% 0.79/1.00         <= ((![X49 : $i, X50 : $i]:
% 0.79/1.00                (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.79/1.00                 | ~ (l1_pre_topc @ X50)
% 0.79/1.00                 | ~ (v2_pre_topc @ X50))))),
% 0.79/1.00      inference('split', [status(esa)], ['6'])).
% 0.79/1.00  thf('10', plain,
% 0.79/1.00      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.79/1.00         <= ((![X49 : $i, X50 : $i]:
% 0.79/1.00                (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.79/1.00                 | ~ (l1_pre_topc @ X50)
% 0.79/1.00                 | ~ (v2_pre_topc @ X50))))),
% 0.79/1.00      inference('sup-', [status(thm)], ['8', '9'])).
% 0.79/1.00  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf('13', plain,
% 0.79/1.00      (~
% 0.79/1.00       (![X49 : $i, X50 : $i]:
% 0.79/1.00          (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.79/1.00           | ~ (l1_pre_topc @ X50)
% 0.79/1.00           | ~ (v2_pre_topc @ X50)))),
% 0.79/1.00      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.79/1.00  thf('14', plain,
% 0.79/1.00      ((![X47 : $i, X48 : $i]:
% 0.79/1.00          (~ (l1_pre_topc @ X47)
% 0.79/1.00           | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.79/1.00           | ~ (v3_pre_topc @ X48 @ X47)
% 0.79/1.00           | ((k1_tops_1 @ X47 @ X48) = (X48)))) | 
% 0.79/1.00       (![X49 : $i, X50 : $i]:
% 0.79/1.00          (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.79/1.00           | ~ (l1_pre_topc @ X50)
% 0.79/1.00           | ~ (v2_pre_topc @ X50)))),
% 0.79/1.00      inference('split', [status(esa)], ['6'])).
% 0.79/1.00  thf('15', plain,
% 0.79/1.00      ((![X47 : $i, X48 : $i]:
% 0.79/1.00          (~ (l1_pre_topc @ X47)
% 0.79/1.00           | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.79/1.00           | ~ (v3_pre_topc @ X48 @ X47)
% 0.79/1.00           | ((k1_tops_1 @ X47 @ X48) = (X48))))),
% 0.79/1.00      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 0.79/1.00  thf('16', plain,
% 0.79/1.00      (![X47 : $i, X48 : $i]:
% 0.79/1.00         (~ (l1_pre_topc @ X47)
% 0.79/1.00          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.79/1.00          | ~ (v3_pre_topc @ X48 @ X47)
% 0.79/1.00          | ((k1_tops_1 @ X47 @ X48) = (X48)))),
% 0.79/1.00      inference('simpl_trail', [status(thm)], ['7', '15'])).
% 0.79/1.00  thf('17', plain,
% 0.79/1.00      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.79/1.00        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.79/1.00        | ~ (l1_pre_topc @ sk_A))),
% 0.79/1.00      inference('sup-', [status(thm)], ['5', '16'])).
% 0.79/1.00  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf('19', plain,
% 0.79/1.00      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.79/1.00      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/1.00  thf('20', plain,
% 0.79/1.00      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.79/1.00         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['4', '19'])).
% 0.79/1.00  thf('21', plain,
% 0.79/1.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf(l78_tops_1, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( l1_pre_topc @ A ) =>
% 0.79/1.00       ( ![B:$i]:
% 0.79/1.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.79/1.00           ( ( k2_tops_1 @ A @ B ) =
% 0.79/1.00             ( k7_subset_1 @
% 0.79/1.00               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.79/1.00               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.79/1.00  thf('22', plain,
% 0.79/1.00      (![X45 : $i, X46 : $i]:
% 0.79/1.00         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.79/1.00          | ((k2_tops_1 @ X46 @ X45)
% 0.79/1.00              = (k7_subset_1 @ (u1_struct_0 @ X46) @ 
% 0.79/1.00                 (k2_pre_topc @ X46 @ X45) @ (k1_tops_1 @ X46 @ X45)))
% 0.79/1.00          | ~ (l1_pre_topc @ X46))),
% 0.79/1.00      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.79/1.00  thf('23', plain,
% 0.79/1.00      ((~ (l1_pre_topc @ sk_A)
% 0.79/1.00        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.00            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.00               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.79/1.00      inference('sup-', [status(thm)], ['21', '22'])).
% 0.79/1.00  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf('25', plain,
% 0.79/1.00      (((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.00         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.79/1.00            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.79/1.00      inference('demod', [status(thm)], ['23', '24'])).
% 0.79/1.00  thf('26', plain,
% 0.79/1.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf(dt_k2_pre_topc, axiom,
% 0.79/1.00    (![A:$i,B:$i]:
% 0.79/1.00     ( ( ( l1_pre_topc @ A ) & 
% 0.79/1.00         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.79/1.00       ( m1_subset_1 @
% 0.79/1.00         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.79/1.00  thf('27', plain,
% 0.79/1.00      (![X39 : $i, X40 : $i]:
% 0.79/1.00         (~ (l1_pre_topc @ X39)
% 0.79/1.00          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.79/1.00          | (m1_subset_1 @ (k2_pre_topc @ X39 @ X40) @ 
% 0.79/1.00             (k1_zfmisc_1 @ (u1_struct_0 @ X39))))),
% 0.79/1.00      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.79/1.00  thf('28', plain,
% 0.79/1.00      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.79/1.00         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.79/1.00        | ~ (l1_pre_topc @ sk_A))),
% 0.79/1.00      inference('sup-', [status(thm)], ['26', '27'])).
% 0.79/1.00  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf('30', plain,
% 0.79/1.00      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.79/1.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.79/1.00      inference('demod', [status(thm)], ['28', '29'])).
% 0.79/1.00  thf(redefinition_k7_subset_1, axiom,
% 0.79/1.00    (![A:$i,B:$i,C:$i]:
% 0.79/1.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.79/1.00       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.79/1.00  thf('31', plain,
% 0.79/1.00      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.79/1.00         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.79/1.00          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 0.79/1.00      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.79/1.00  thf(redefinition_k6_subset_1, axiom,
% 0.79/1.00    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.79/1.00  thf('32', plain,
% 0.79/1.00      (![X26 : $i, X27 : $i]:
% 0.79/1.00         ((k6_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))),
% 0.79/1.00      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.79/1.00  thf('33', plain,
% 0.79/1.00      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.79/1.00         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.79/1.00          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k6_subset_1 @ X28 @ X30)))),
% 0.79/1.00      inference('demod', [status(thm)], ['31', '32'])).
% 0.79/1.00  thf('34', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.79/1.00           X0) = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['30', '33'])).
% 0.79/1.01  thf('35', plain,
% 0.79/1.01      (((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.79/1.01            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['25', '34'])).
% 0.79/1.01  thf('36', plain,
% 0.79/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.79/1.01         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['20', '35'])).
% 0.79/1.01  thf('37', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.79/1.01           X0) = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['30', '33'])).
% 0.79/1.01  thf('38', plain,
% 0.79/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.01              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.79/1.01         <= (~
% 0.79/1.01             (((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.01                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.79/1.01      inference('split', [status(esa)], ['0'])).
% 0.79/1.01  thf('39', plain,
% 0.79/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01          != (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.79/1.01         <= (~
% 0.79/1.01             (((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.01                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['37', '38'])).
% 0.79/1.01  thf('40', plain,
% 0.79/1.01      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.79/1.01         <= (~
% 0.79/1.01             (((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.01                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.79/1.01             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['36', '39'])).
% 0.79/1.01  thf('41', plain,
% 0.79/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.01             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.79/1.01       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.79/1.01      inference('simplify', [status(thm)], ['40'])).
% 0.79/1.01  thf('42', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.79/1.01      inference('sat_resolution*', [status(thm)], ['2', '41'])).
% 0.79/1.01  thf('43', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.79/1.01      inference('simpl_trail', [status(thm)], ['1', '42'])).
% 0.79/1.01  thf('44', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('45', plain,
% 0.79/1.01      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.79/1.01         (~ (l1_pre_topc @ X47)
% 0.79/1.01          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.79/1.01          | ((k1_tops_1 @ X50 @ X49) != (X49))
% 0.79/1.01          | (v3_pre_topc @ X49 @ X50)
% 0.79/1.01          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.79/1.01          | ~ (l1_pre_topc @ X50)
% 0.79/1.01          | ~ (v2_pre_topc @ X50))),
% 0.79/1.01      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.79/1.01  thf('46', plain,
% 0.79/1.01      ((![X49 : $i, X50 : $i]:
% 0.79/1.01          (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.79/1.01           | ~ (l1_pre_topc @ X50)
% 0.79/1.01           | ~ (v2_pre_topc @ X50)
% 0.79/1.01           | ((k1_tops_1 @ X50 @ X49) != (X49))
% 0.79/1.01           | (v3_pre_topc @ X49 @ X50)))
% 0.79/1.01         <= ((![X49 : $i, X50 : $i]:
% 0.79/1.01                (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.79/1.01                 | ~ (l1_pre_topc @ X50)
% 0.79/1.01                 | ~ (v2_pre_topc @ X50)
% 0.79/1.01                 | ((k1_tops_1 @ X50 @ X49) != (X49))
% 0.79/1.01                 | (v3_pre_topc @ X49 @ X50))))),
% 0.79/1.01      inference('split', [status(esa)], ['45'])).
% 0.79/1.01  thf('47', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('48', plain,
% 0.79/1.01      ((![X47 : $i, X48 : $i]:
% 0.79/1.01          (~ (l1_pre_topc @ X47)
% 0.79/1.01           | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))))
% 0.79/1.01         <= ((![X47 : $i, X48 : $i]:
% 0.79/1.01                (~ (l1_pre_topc @ X47)
% 0.79/1.01                 | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47))))))),
% 0.79/1.01      inference('split', [status(esa)], ['45'])).
% 0.79/1.01  thf('49', plain,
% 0.79/1.01      ((~ (l1_pre_topc @ sk_A))
% 0.79/1.01         <= ((![X47 : $i, X48 : $i]:
% 0.79/1.01                (~ (l1_pre_topc @ X47)
% 0.79/1.01                 | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47))))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['47', '48'])).
% 0.79/1.01  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('51', plain,
% 0.79/1.01      (~
% 0.79/1.01       (![X47 : $i, X48 : $i]:
% 0.79/1.01          (~ (l1_pre_topc @ X47)
% 0.79/1.01           | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))))),
% 0.79/1.01      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/1.01  thf('52', plain,
% 0.79/1.01      ((![X49 : $i, X50 : $i]:
% 0.79/1.01          (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.79/1.01           | ~ (l1_pre_topc @ X50)
% 0.79/1.01           | ~ (v2_pre_topc @ X50)
% 0.79/1.01           | ((k1_tops_1 @ X50 @ X49) != (X49))
% 0.79/1.01           | (v3_pre_topc @ X49 @ X50))) | 
% 0.79/1.01       (![X47 : $i, X48 : $i]:
% 0.79/1.01          (~ (l1_pre_topc @ X47)
% 0.79/1.01           | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))))),
% 0.79/1.01      inference('split', [status(esa)], ['45'])).
% 0.79/1.01  thf('53', plain,
% 0.79/1.01      ((![X49 : $i, X50 : $i]:
% 0.79/1.01          (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.79/1.01           | ~ (l1_pre_topc @ X50)
% 0.79/1.01           | ~ (v2_pre_topc @ X50)
% 0.79/1.01           | ((k1_tops_1 @ X50 @ X49) != (X49))
% 0.79/1.01           | (v3_pre_topc @ X49 @ X50)))),
% 0.79/1.01      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.79/1.01  thf('54', plain,
% 0.79/1.01      (![X49 : $i, X50 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.79/1.01          | ~ (l1_pre_topc @ X50)
% 0.79/1.01          | ~ (v2_pre_topc @ X50)
% 0.79/1.01          | ((k1_tops_1 @ X50 @ X49) != (X49))
% 0.79/1.01          | (v3_pre_topc @ X49 @ X50))),
% 0.79/1.01      inference('simpl_trail', [status(thm)], ['46', '53'])).
% 0.79/1.01  thf('55', plain,
% 0.79/1.01      (((v3_pre_topc @ sk_B @ sk_A)
% 0.79/1.01        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 0.79/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.79/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.79/1.01      inference('sup-', [status(thm)], ['44', '54'])).
% 0.79/1.01  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('58', plain,
% 0.79/1.01      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.79/1.01  thf('59', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(t74_tops_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( l1_pre_topc @ A ) =>
% 0.79/1.01       ( ![B:$i]:
% 0.79/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.79/1.01           ( ( k1_tops_1 @ A @ B ) =
% 0.79/1.01             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.79/1.01  thf('60', plain,
% 0.79/1.01      (![X53 : $i, X54 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 0.79/1.01          | ((k1_tops_1 @ X54 @ X53)
% 0.79/1.01              = (k7_subset_1 @ (u1_struct_0 @ X54) @ X53 @ 
% 0.79/1.01                 (k2_tops_1 @ X54 @ X53)))
% 0.79/1.01          | ~ (l1_pre_topc @ X54))),
% 0.79/1.01      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.79/1.01  thf('61', plain,
% 0.79/1.01      ((~ (l1_pre_topc @ sk_A)
% 0.79/1.01        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.79/1.01            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.79/1.01               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['59', '60'])).
% 0.79/1.01  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('63', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('64', plain,
% 0.79/1.01      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.79/1.01          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k6_subset_1 @ X28 @ X30)))),
% 0.79/1.01      inference('demod', [status(thm)], ['31', '32'])).
% 0.79/1.01  thf('65', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.79/1.01           = (k6_subset_1 @ sk_B @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['63', '64'])).
% 0.79/1.01  thf('66', plain,
% 0.79/1.01      (((k1_tops_1 @ sk_A @ sk_B)
% 0.79/1.01         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.79/1.01  thf(t39_xboole_1, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.79/1.01  thf('67', plain,
% 0.79/1.01      (![X7 : $i, X8 : $i]:
% 0.79/1.01         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.79/1.01           = (k2_xboole_0 @ X7 @ X8))),
% 0.79/1.01      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.79/1.01  thf('68', plain,
% 0.79/1.01      (![X26 : $i, X27 : $i]:
% 0.79/1.01         ((k6_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.79/1.01  thf('69', plain,
% 0.79/1.01      (![X7 : $i, X8 : $i]:
% 0.79/1.01         ((k2_xboole_0 @ X7 @ (k6_subset_1 @ X8 @ X7))
% 0.79/1.01           = (k2_xboole_0 @ X7 @ X8))),
% 0.79/1.01      inference('demod', [status(thm)], ['67', '68'])).
% 0.79/1.01  thf('70', plain,
% 0.79/1.01      (((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.79/1.01         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['66', '69'])).
% 0.79/1.01  thf(commutativity_k2_xboole_0, axiom,
% 0.79/1.01    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.79/1.01  thf('71', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.79/1.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.79/1.01  thf('72', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.79/1.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.79/1.01  thf('73', plain,
% 0.79/1.01      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.79/1.01         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.79/1.01  thf('74', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(dt_k2_tops_1, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( ( l1_pre_topc @ A ) & 
% 0.79/1.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.79/1.01       ( m1_subset_1 @
% 0.79/1.01         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.79/1.01  thf('75', plain,
% 0.79/1.01      (![X41 : $i, X42 : $i]:
% 0.79/1.01         (~ (l1_pre_topc @ X41)
% 0.79/1.01          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.79/1.01          | (m1_subset_1 @ (k2_tops_1 @ X41 @ X42) @ 
% 0.79/1.01             (k1_zfmisc_1 @ (u1_struct_0 @ X41))))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.79/1.01  thf('76', plain,
% 0.79/1.01      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.79/1.01         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.79/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.79/1.01      inference('sup-', [status(thm)], ['74', '75'])).
% 0.79/1.01  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('78', plain,
% 0.79/1.01      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['76', '77'])).
% 0.79/1.01  thf('79', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(redefinition_k4_subset_1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.79/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.79/1.01       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.79/1.01  thf('80', plain,
% 0.79/1.01      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.79/1.01          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24))
% 0.79/1.01          | ((k4_subset_1 @ X24 @ X23 @ X25) = (k2_xboole_0 @ X23 @ X25)))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.79/1.01  thf('81', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.79/1.01            = (k2_xboole_0 @ sk_B @ X0))
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['79', '80'])).
% 0.79/1.01  thf('82', plain,
% 0.79/1.01      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.79/1.01         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['78', '81'])).
% 0.79/1.01  thf('83', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(t65_tops_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( l1_pre_topc @ A ) =>
% 0.79/1.01       ( ![B:$i]:
% 0.79/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.79/1.01           ( ( k2_pre_topc @ A @ B ) =
% 0.79/1.01             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.79/1.01  thf('84', plain,
% 0.79/1.01      (![X51 : $i, X52 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.79/1.01          | ((k2_pre_topc @ X52 @ X51)
% 0.79/1.01              = (k4_subset_1 @ (u1_struct_0 @ X52) @ X51 @ 
% 0.79/1.01                 (k2_tops_1 @ X52 @ X51)))
% 0.79/1.01          | ~ (l1_pre_topc @ X52))),
% 0.79/1.01      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.79/1.01  thf('85', plain,
% 0.79/1.01      ((~ (l1_pre_topc @ sk_A)
% 0.79/1.01        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.79/1.01            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.79/1.01               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['83', '84'])).
% 0.79/1.01  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('87', plain,
% 0.79/1.01      (((k2_pre_topc @ sk_A @ sk_B)
% 0.79/1.01         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.79/1.01            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['85', '86'])).
% 0.79/1.01  thf('88', plain,
% 0.79/1.01      (((k2_pre_topc @ sk_A @ sk_B)
% 0.79/1.01         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['82', '87'])).
% 0.79/1.01  thf('89', plain,
% 0.79/1.01      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.79/1.01         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['73', '88'])).
% 0.79/1.01  thf('90', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.79/1.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.79/1.01  thf(dt_k6_subset_1, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.79/1.01  thf('91', plain,
% 0.79/1.01      (![X16 : $i, X17 : $i]:
% 0.79/1.01         (m1_subset_1 @ (k6_subset_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.79/1.01  thf(t3_subset, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.79/1.01  thf('92', plain,
% 0.79/1.01      (![X36 : $i, X37 : $i]:
% 0.79/1.01         ((r1_tarski @ X36 @ X37) | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 0.79/1.01      inference('cnf', [status(esa)], [t3_subset])).
% 0.79/1.01  thf('93', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.79/1.01      inference('sup-', [status(thm)], ['91', '92'])).
% 0.79/1.01  thf(t44_xboole_1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.79/1.01       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.79/1.01  thf('94', plain,
% 0.79/1.01      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.79/1.01         ((r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 0.79/1.01          | ~ (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11))),
% 0.79/1.01      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.79/1.01  thf('95', plain,
% 0.79/1.01      (![X26 : $i, X27 : $i]:
% 0.79/1.01         ((k6_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.79/1.01  thf('96', plain,
% 0.79/1.01      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.79/1.01         ((r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 0.79/1.01          | ~ (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X11))),
% 0.79/1.01      inference('demod', [status(thm)], ['94', '95'])).
% 0.79/1.01  thf('97', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['93', '96'])).
% 0.79/1.01  thf('98', plain,
% 0.79/1.01      (![X36 : $i, X38 : $i]:
% 0.79/1.01         ((m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X38)) | ~ (r1_tarski @ X36 @ X38))),
% 0.79/1.01      inference('cnf', [status(esa)], [t3_subset])).
% 0.79/1.01  thf('99', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['97', '98'])).
% 0.79/1.01  thf(involutiveness_k3_subset_1, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.79/1.01       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.79/1.01  thf('100', plain,
% 0.79/1.01      (![X21 : $i, X22 : $i]:
% 0.79/1.01         (((k3_subset_1 @ X22 @ (k3_subset_1 @ X22 @ X21)) = (X21))
% 0.79/1.01          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.79/1.01      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.79/1.01  thf('101', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.79/1.01           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)) = (X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['99', '100'])).
% 0.79/1.01  thf('102', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.79/1.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.79/1.01  thf('103', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.79/1.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.79/1.01  thf('104', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['97', '98'])).
% 0.79/1.01  thf('105', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['103', '104'])).
% 0.79/1.01  thf(d5_subset_1, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.79/1.01       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.79/1.01  thf('106', plain,
% 0.79/1.01      (![X12 : $i, X13 : $i]:
% 0.79/1.01         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 0.79/1.01          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.79/1.01      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.79/1.01  thf('107', plain,
% 0.79/1.01      (![X26 : $i, X27 : $i]:
% 0.79/1.01         ((k6_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.79/1.01  thf('108', plain,
% 0.79/1.01      (![X12 : $i, X13 : $i]:
% 0.79/1.01         (((k3_subset_1 @ X12 @ X13) = (k6_subset_1 @ X12 @ X13))
% 0.79/1.01          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.79/1.01      inference('demod', [status(thm)], ['106', '107'])).
% 0.79/1.01  thf('109', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.79/1.01           = (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 0.79/1.01      inference('sup-', [status(thm)], ['105', '108'])).
% 0.79/1.01  thf('110', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.79/1.01           = (k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.79/1.01      inference('sup+', [status(thm)], ['102', '109'])).
% 0.79/1.01  thf('111', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.79/1.01           (k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)) = (X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['101', '110'])).
% 0.79/1.01  thf('112', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.79/1.01           (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 0.79/1.01      inference('sup+', [status(thm)], ['90', '111'])).
% 0.79/1.01  thf('113', plain,
% 0.79/1.01      (![X16 : $i, X17 : $i]:
% 0.79/1.01         (m1_subset_1 @ (k6_subset_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.79/1.01  thf('114', plain,
% 0.79/1.01      (![X12 : $i, X13 : $i]:
% 0.79/1.01         (((k3_subset_1 @ X12 @ X13) = (k6_subset_1 @ X12 @ X13))
% 0.79/1.01          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.79/1.01      inference('demod', [status(thm)], ['106', '107'])).
% 0.79/1.01  thf('115', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.79/1.01           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['113', '114'])).
% 0.79/1.01  thf('116', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         ((k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.79/1.01           (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 0.79/1.01      inference('demod', [status(thm)], ['112', '115'])).
% 0.79/1.01  thf('117', plain,
% 0.79/1.01      (((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.79/1.01         (k6_subset_1 @ 
% 0.79/1.01          (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.79/1.01          (k1_tops_1 @ sk_A @ sk_B)))
% 0.79/1.01         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['89', '116'])).
% 0.79/1.01  thf('118', plain,
% 0.79/1.01      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.79/1.01         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['73', '88'])).
% 0.79/1.01  thf('119', plain,
% 0.79/1.01      (((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.79/1.01            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['25', '34'])).
% 0.79/1.01  thf('120', plain,
% 0.79/1.01      (((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.79/1.01         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.79/1.01  thf('121', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.79/1.01           X0) = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['30', '33'])).
% 0.79/1.01  thf('122', plain,
% 0.79/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.01             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.79/1.01         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.01                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.79/1.01      inference('split', [status(esa)], ['3'])).
% 0.79/1.01  thf('123', plain,
% 0.79/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.79/1.01         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.01                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.79/1.01      inference('sup+', [status(thm)], ['121', '122'])).
% 0.79/1.01  thf('124', plain,
% 0.79/1.01      (((k2_pre_topc @ sk_A @ sk_B)
% 0.79/1.01         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['82', '87'])).
% 0.79/1.01  thf('125', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.79/1.01           (k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)) = (X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['101', '110'])).
% 0.79/1.01  thf('126', plain,
% 0.79/1.01      (((k3_subset_1 @ (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.79/1.01         (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['124', '125'])).
% 0.79/1.01  thf('127', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.79/1.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.79/1.01  thf('128', plain,
% 0.79/1.01      (((k2_pre_topc @ sk_A @ sk_B)
% 0.79/1.01         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['82', '87'])).
% 0.79/1.01  thf('129', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.79/1.01           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['113', '114'])).
% 0.79/1.01  thf('130', plain,
% 0.79/1.01      (((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.79/1.01         (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.79/1.01  thf('131', plain,
% 0.79/1.01      ((((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.79/1.01          = (sk_B)))
% 0.79/1.01         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.01                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.79/1.01      inference('sup+', [status(thm)], ['123', '130'])).
% 0.79/1.01  thf('132', plain,
% 0.79/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.01             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.79/1.01       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.79/1.01      inference('split', [status(esa)], ['3'])).
% 0.79/1.01  thf('133', plain,
% 0.79/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.79/1.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.79/1.01             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.79/1.01      inference('sat_resolution*', [status(thm)], ['2', '41', '132'])).
% 0.79/1.01  thf('134', plain,
% 0.79/1.01      (((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.79/1.01         = (sk_B))),
% 0.79/1.01      inference('simpl_trail', [status(thm)], ['131', '133'])).
% 0.79/1.01  thf('135', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['120', '134'])).
% 0.79/1.01  thf('136', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['58', '135'])).
% 0.79/1.01  thf('137', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.79/1.01      inference('simplify', [status(thm)], ['136'])).
% 0.79/1.01  thf('138', plain, ($false), inference('demod', [status(thm)], ['43', '137'])).
% 0.79/1.01  
% 0.79/1.01  % SZS output end Refutation
% 0.79/1.01  
% 0.79/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
