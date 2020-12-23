%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3c7MvKrRFz

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:34 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 281 expanded)
%              Number of leaves         :   22 (  84 expanded)
%              Depth                    :   18
%              Number of atoms          : 1201 (4339 expanded)
%              Number of equality atoms :   74 ( 222 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X27 )
      | ( ( k1_tops_1 @ X27 @ X28 )
        = X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('7',plain,
    ( ! [X27: $i,X28: $i] :
        ( ~ ( l1_pre_topc @ X27 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( v3_pre_topc @ X28 @ X27 )
        | ( ( k1_tops_1 @ X27 @ X28 )
          = X28 ) )
   <= ! [X27: $i,X28: $i] :
        ( ~ ( l1_pre_topc @ X27 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( v3_pre_topc @ X28 @ X27 )
        | ( ( k1_tops_1 @ X27 @ X28 )
          = X28 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X29: $i,X30: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( l1_pre_topc @ X30 )
        | ~ ( v2_pre_topc @ X30 ) )
   <= ! [X29: $i,X30: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( l1_pre_topc @ X30 )
        | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X29: $i,X30: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( l1_pre_topc @ X30 )
        | ~ ( v2_pre_topc @ X30 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ! [X29: $i,X30: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( l1_pre_topc @ X30 )
        | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ! [X27: $i,X28: $i] :
        ( ~ ( l1_pre_topc @ X27 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( v3_pre_topc @ X28 @ X27 )
        | ( ( k1_tops_1 @ X27 @ X28 )
          = X28 ) )
    | ! [X29: $i,X30: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( l1_pre_topc @ X30 )
        | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X27 )
      | ( ( k1_tops_1 @ X27 @ X28 )
        = X28 ) ) ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X27 )
      | ( ( k1_tops_1 @ X27 @ X28 )
        = X28 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k2_tops_1 @ X24 @ X23 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k2_pre_topc @ X24 @ X23 ) @ ( k1_tops_1 @ X24 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('27',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','31'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['20','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','38'])).

thf('40',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k1_tops_1 @ X30 @ X29 )
       != X29 )
      | ( v3_pre_topc @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('43',plain,
    ( ! [X29: $i,X30: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( l1_pre_topc @ X30 )
        | ~ ( v2_pre_topc @ X30 )
        | ( ( k1_tops_1 @ X30 @ X29 )
         != X29 )
        | ( v3_pre_topc @ X29 @ X30 ) )
   <= ! [X29: $i,X30: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( l1_pre_topc @ X30 )
        | ~ ( v2_pre_topc @ X30 )
        | ( ( k1_tops_1 @ X30 @ X29 )
         != X29 )
        | ( v3_pre_topc @ X29 @ X30 ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ! [X27: $i,X28: $i] :
        ( ~ ( l1_pre_topc @ X27 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
   <= ! [X27: $i,X28: $i] :
        ( ~ ( l1_pre_topc @ X27 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X27: $i,X28: $i] :
        ( ~ ( l1_pre_topc @ X27 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ! [X27: $i,X28: $i] :
        ( ~ ( l1_pre_topc @ X27 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X29: $i,X30: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( l1_pre_topc @ X30 )
        | ~ ( v2_pre_topc @ X30 )
        | ( ( k1_tops_1 @ X30 @ X29 )
         != X29 )
        | ( v3_pre_topc @ X29 @ X30 ) )
    | ! [X27: $i,X28: $i] :
        ( ~ ( l1_pre_topc @ X27 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('50',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( ( k1_tops_1 @ X30 @ X29 )
       != X29 )
      | ( v3_pre_topc @ X29 @ X30 ) ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( ( k1_tops_1 @ X30 @ X29 )
       != X29 )
      | ( v3_pre_topc @ X29 @ X30 ) ) ),
    inference(simpl_trail,[status(thm)],['43','50'])).

thf('52',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('57',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k1_tops_1 @ X35 @ X34 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X35 ) @ X34 @ ( k2_tops_1 @ X35 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('63',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['63'])).

thf('66',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['63'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('72',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('73',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('75',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( X0
          = ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ ( sk_D @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,
    ( ( ( sk_B
        = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ( sk_B
        = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','77'])).

thf('79',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('81',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','38','80'])).

thf('82',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['79','81'])).

thf('83',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['58','59','62','82'])).

thf('84',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['55','83'])).

thf('85',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['40','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3c7MvKrRFz
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:28:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.53/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.71  % Solved by: fo/fo7.sh
% 0.53/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.71  % done 306 iterations in 0.288s
% 0.53/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.71  % SZS output start Refutation
% 0.53/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.71  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.53/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.53/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.71  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.53/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.53/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.71  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.53/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.71  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.53/0.71  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.53/0.71  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.53/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.71  thf(t76_tops_1, conjecture,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.71       ( ![B:$i]:
% 0.53/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.71           ( ( v3_pre_topc @ B @ A ) <=>
% 0.53/0.71             ( ( k2_tops_1 @ A @ B ) =
% 0.53/0.71               ( k7_subset_1 @
% 0.53/0.71                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.53/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.71    (~( ![A:$i]:
% 0.53/0.71        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.71          ( ![B:$i]:
% 0.53/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.71              ( ( v3_pre_topc @ B @ A ) <=>
% 0.53/0.71                ( ( k2_tops_1 @ A @ B ) =
% 0.53/0.71                  ( k7_subset_1 @
% 0.53/0.71                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.53/0.71    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.53/0.71  thf('0', plain,
% 0.53/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.71              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.53/0.71        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('1', plain,
% 0.53/0.71      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.71      inference('split', [status(esa)], ['0'])).
% 0.53/0.71  thf('2', plain,
% 0.53/0.71      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.53/0.71       ~
% 0.53/0.71       (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.71             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.53/0.71      inference('split', [status(esa)], ['0'])).
% 0.53/0.71  thf('3', plain,
% 0.53/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.71             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.53/0.71        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('4', plain,
% 0.53/0.71      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.71      inference('split', [status(esa)], ['3'])).
% 0.53/0.71  thf('5', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t55_tops_1, axiom,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.71       ( ![B:$i]:
% 0.53/0.71         ( ( l1_pre_topc @ B ) =>
% 0.53/0.71           ( ![C:$i]:
% 0.53/0.71             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.71               ( ![D:$i]:
% 0.53/0.71                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.53/0.71                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.53/0.71                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.53/0.71                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.53/0.71                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.71  thf('6', plain,
% 0.53/0.71      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.53/0.71         (~ (l1_pre_topc @ X27)
% 0.53/0.71          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.53/0.71          | ~ (v3_pre_topc @ X28 @ X27)
% 0.53/0.71          | ((k1_tops_1 @ X27 @ X28) = (X28))
% 0.53/0.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.53/0.71          | ~ (l1_pre_topc @ X30)
% 0.53/0.71          | ~ (v2_pre_topc @ X30))),
% 0.53/0.71      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.53/0.71  thf('7', plain,
% 0.53/0.71      ((![X27 : $i, X28 : $i]:
% 0.53/0.71          (~ (l1_pre_topc @ X27)
% 0.53/0.71           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.53/0.71           | ~ (v3_pre_topc @ X28 @ X27)
% 0.53/0.71           | ((k1_tops_1 @ X27 @ X28) = (X28))))
% 0.53/0.71         <= ((![X27 : $i, X28 : $i]:
% 0.53/0.71                (~ (l1_pre_topc @ X27)
% 0.53/0.71                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.53/0.71                 | ~ (v3_pre_topc @ X28 @ X27)
% 0.53/0.71                 | ((k1_tops_1 @ X27 @ X28) = (X28)))))),
% 0.53/0.71      inference('split', [status(esa)], ['6'])).
% 0.53/0.71  thf('8', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('9', plain,
% 0.53/0.71      ((![X29 : $i, X30 : $i]:
% 0.53/0.71          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.53/0.71           | ~ (l1_pre_topc @ X30)
% 0.53/0.71           | ~ (v2_pre_topc @ X30)))
% 0.53/0.71         <= ((![X29 : $i, X30 : $i]:
% 0.53/0.71                (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.53/0.71                 | ~ (l1_pre_topc @ X30)
% 0.53/0.71                 | ~ (v2_pre_topc @ X30))))),
% 0.53/0.71      inference('split', [status(esa)], ['6'])).
% 0.53/0.71  thf('10', plain,
% 0.53/0.71      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.53/0.71         <= ((![X29 : $i, X30 : $i]:
% 0.53/0.71                (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.53/0.71                 | ~ (l1_pre_topc @ X30)
% 0.53/0.71                 | ~ (v2_pre_topc @ X30))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.71  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('13', plain,
% 0.53/0.71      (~
% 0.53/0.71       (![X29 : $i, X30 : $i]:
% 0.53/0.71          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.53/0.71           | ~ (l1_pre_topc @ X30)
% 0.53/0.71           | ~ (v2_pre_topc @ X30)))),
% 0.53/0.71      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.53/0.71  thf('14', plain,
% 0.53/0.71      ((![X27 : $i, X28 : $i]:
% 0.53/0.71          (~ (l1_pre_topc @ X27)
% 0.53/0.71           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.53/0.71           | ~ (v3_pre_topc @ X28 @ X27)
% 0.53/0.71           | ((k1_tops_1 @ X27 @ X28) = (X28)))) | 
% 0.53/0.71       (![X29 : $i, X30 : $i]:
% 0.53/0.71          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.53/0.71           | ~ (l1_pre_topc @ X30)
% 0.53/0.71           | ~ (v2_pre_topc @ X30)))),
% 0.53/0.71      inference('split', [status(esa)], ['6'])).
% 0.53/0.71  thf('15', plain,
% 0.53/0.71      ((![X27 : $i, X28 : $i]:
% 0.53/0.71          (~ (l1_pre_topc @ X27)
% 0.53/0.71           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.53/0.71           | ~ (v3_pre_topc @ X28 @ X27)
% 0.53/0.71           | ((k1_tops_1 @ X27 @ X28) = (X28))))),
% 0.53/0.71      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 0.53/0.71  thf('16', plain,
% 0.53/0.71      (![X27 : $i, X28 : $i]:
% 0.53/0.71         (~ (l1_pre_topc @ X27)
% 0.53/0.71          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.53/0.71          | ~ (v3_pre_topc @ X28 @ X27)
% 0.53/0.71          | ((k1_tops_1 @ X27 @ X28) = (X28)))),
% 0.53/0.71      inference('simpl_trail', [status(thm)], ['7', '15'])).
% 0.53/0.71  thf('17', plain,
% 0.53/0.71      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.53/0.71        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.53/0.71        | ~ (l1_pre_topc @ sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['5', '16'])).
% 0.53/0.71  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('19', plain,
% 0.53/0.71      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.53/0.71      inference('demod', [status(thm)], ['17', '18'])).
% 0.53/0.71  thf('20', plain,
% 0.53/0.71      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.53/0.71         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['4', '19'])).
% 0.53/0.71  thf('21', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(l78_tops_1, axiom,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( l1_pre_topc @ A ) =>
% 0.53/0.71       ( ![B:$i]:
% 0.53/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.71           ( ( k2_tops_1 @ A @ B ) =
% 0.53/0.71             ( k7_subset_1 @
% 0.53/0.71               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.53/0.71               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.53/0.71  thf('22', plain,
% 0.53/0.71      (![X23 : $i, X24 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.53/0.71          | ((k2_tops_1 @ X24 @ X23)
% 0.53/0.71              = (k7_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.53/0.71                 (k2_pre_topc @ X24 @ X23) @ (k1_tops_1 @ X24 @ X23)))
% 0.53/0.71          | ~ (l1_pre_topc @ X24))),
% 0.53/0.71      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.53/0.71  thf('23', plain,
% 0.53/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.71        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.71               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['21', '22'])).
% 0.53/0.71  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('25', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(dt_k2_pre_topc, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( l1_pre_topc @ A ) & 
% 0.53/0.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.71       ( m1_subset_1 @
% 0.53/0.71         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.53/0.71  thf('26', plain,
% 0.53/0.71      (![X19 : $i, X20 : $i]:
% 0.53/0.71         (~ (l1_pre_topc @ X19)
% 0.53/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.53/0.71          | (m1_subset_1 @ (k2_pre_topc @ X19 @ X20) @ 
% 0.53/0.71             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.53/0.71      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.53/0.71  thf('27', plain,
% 0.53/0.71      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.53/0.71         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.71        | ~ (l1_pre_topc @ sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.53/0.71  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('29', plain,
% 0.53/0.71      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.53/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('demod', [status(thm)], ['27', '28'])).
% 0.53/0.71  thf(redefinition_k7_subset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.71       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.53/0.71  thf('30', plain,
% 0.53/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.53/0.71          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.53/0.71      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.53/0.71  thf('31', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.53/0.71           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.71  thf('32', plain,
% 0.53/0.71      (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.53/0.71            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('demod', [status(thm)], ['23', '24', '31'])).
% 0.53/0.71  thf('33', plain,
% 0.53/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.53/0.71         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.71      inference('sup+', [status(thm)], ['20', '32'])).
% 0.53/0.71  thf('34', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.53/0.71           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.71  thf('35', plain,
% 0.53/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.71              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.53/0.71         <= (~
% 0.53/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.71                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.53/0.71      inference('split', [status(esa)], ['0'])).
% 0.53/0.71  thf('36', plain,
% 0.53/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.53/0.71         <= (~
% 0.53/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.71                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.71  thf('37', plain,
% 0.53/0.71      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.53/0.71         <= (~
% 0.53/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.71                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.53/0.71             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['33', '36'])).
% 0.53/0.71  thf('38', plain,
% 0.53/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.71             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.53/0.71       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.53/0.71      inference('simplify', [status(thm)], ['37'])).
% 0.53/0.71  thf('39', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.53/0.71      inference('sat_resolution*', [status(thm)], ['2', '38'])).
% 0.53/0.71  thf('40', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.53/0.71      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 0.53/0.71  thf('41', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('42', plain,
% 0.53/0.71      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.53/0.71         (~ (l1_pre_topc @ X27)
% 0.53/0.71          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.53/0.71          | ((k1_tops_1 @ X30 @ X29) != (X29))
% 0.53/0.71          | (v3_pre_topc @ X29 @ X30)
% 0.53/0.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.53/0.71          | ~ (l1_pre_topc @ X30)
% 0.53/0.71          | ~ (v2_pre_topc @ X30))),
% 0.53/0.71      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.53/0.71  thf('43', plain,
% 0.53/0.71      ((![X29 : $i, X30 : $i]:
% 0.53/0.71          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.53/0.71           | ~ (l1_pre_topc @ X30)
% 0.53/0.71           | ~ (v2_pre_topc @ X30)
% 0.53/0.71           | ((k1_tops_1 @ X30 @ X29) != (X29))
% 0.53/0.71           | (v3_pre_topc @ X29 @ X30)))
% 0.53/0.71         <= ((![X29 : $i, X30 : $i]:
% 0.53/0.71                (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.53/0.71                 | ~ (l1_pre_topc @ X30)
% 0.53/0.71                 | ~ (v2_pre_topc @ X30)
% 0.53/0.71                 | ((k1_tops_1 @ X30 @ X29) != (X29))
% 0.53/0.71                 | (v3_pre_topc @ X29 @ X30))))),
% 0.53/0.71      inference('split', [status(esa)], ['42'])).
% 0.53/0.71  thf('44', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('45', plain,
% 0.53/0.71      ((![X27 : $i, X28 : $i]:
% 0.53/0.71          (~ (l1_pre_topc @ X27)
% 0.53/0.71           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))))
% 0.53/0.71         <= ((![X27 : $i, X28 : $i]:
% 0.53/0.71                (~ (l1_pre_topc @ X27)
% 0.53/0.71                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))))),
% 0.53/0.71      inference('split', [status(esa)], ['42'])).
% 0.53/0.71  thf('46', plain,
% 0.53/0.71      ((~ (l1_pre_topc @ sk_A))
% 0.53/0.71         <= ((![X27 : $i, X28 : $i]:
% 0.53/0.71                (~ (l1_pre_topc @ X27)
% 0.53/0.71                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['44', '45'])).
% 0.53/0.71  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('48', plain,
% 0.53/0.71      (~
% 0.53/0.71       (![X27 : $i, X28 : $i]:
% 0.53/0.71          (~ (l1_pre_topc @ X27)
% 0.53/0.71           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))))),
% 0.53/0.71      inference('demod', [status(thm)], ['46', '47'])).
% 0.53/0.71  thf('49', plain,
% 0.53/0.71      ((![X29 : $i, X30 : $i]:
% 0.53/0.71          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.53/0.71           | ~ (l1_pre_topc @ X30)
% 0.53/0.71           | ~ (v2_pre_topc @ X30)
% 0.53/0.71           | ((k1_tops_1 @ X30 @ X29) != (X29))
% 0.53/0.71           | (v3_pre_topc @ X29 @ X30))) | 
% 0.53/0.71       (![X27 : $i, X28 : $i]:
% 0.53/0.71          (~ (l1_pre_topc @ X27)
% 0.53/0.71           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))))),
% 0.53/0.71      inference('split', [status(esa)], ['42'])).
% 0.53/0.71  thf('50', plain,
% 0.53/0.71      ((![X29 : $i, X30 : $i]:
% 0.53/0.71          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.53/0.71           | ~ (l1_pre_topc @ X30)
% 0.53/0.71           | ~ (v2_pre_topc @ X30)
% 0.53/0.71           | ((k1_tops_1 @ X30 @ X29) != (X29))
% 0.53/0.71           | (v3_pre_topc @ X29 @ X30)))),
% 0.53/0.71      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.53/0.71  thf('51', plain,
% 0.53/0.71      (![X29 : $i, X30 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.53/0.71          | ~ (l1_pre_topc @ X30)
% 0.53/0.71          | ~ (v2_pre_topc @ X30)
% 0.53/0.71          | ((k1_tops_1 @ X30 @ X29) != (X29))
% 0.53/0.71          | (v3_pre_topc @ X29 @ X30))),
% 0.53/0.71      inference('simpl_trail', [status(thm)], ['43', '50'])).
% 0.53/0.71  thf('52', plain,
% 0.53/0.71      (((v3_pre_topc @ sk_B @ sk_A)
% 0.53/0.71        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 0.53/0.71        | ~ (v2_pre_topc @ sk_A)
% 0.53/0.71        | ~ (l1_pre_topc @ sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['41', '51'])).
% 0.53/0.71  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('55', plain,
% 0.53/0.71      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 0.53/0.71      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.53/0.71  thf('56', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t74_tops_1, axiom,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( l1_pre_topc @ A ) =>
% 0.53/0.71       ( ![B:$i]:
% 0.53/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.71           ( ( k1_tops_1 @ A @ B ) =
% 0.53/0.71             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.53/0.71  thf('57', plain,
% 0.53/0.71      (![X34 : $i, X35 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.53/0.71          | ((k1_tops_1 @ X35 @ X34)
% 0.53/0.71              = (k7_subset_1 @ (u1_struct_0 @ X35) @ X34 @ 
% 0.53/0.71                 (k2_tops_1 @ X35 @ X34)))
% 0.53/0.71          | ~ (l1_pre_topc @ X35))),
% 0.53/0.71      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.53/0.71  thf('58', plain,
% 0.53/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.71        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.53/0.71            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.71               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['56', '57'])).
% 0.53/0.71  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('60', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('61', plain,
% 0.53/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.53/0.71          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.53/0.71      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.53/0.71  thf('62', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.53/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['60', '61'])).
% 0.53/0.71  thf(d5_xboole_0, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.53/0.71       ( ![D:$i]:
% 0.53/0.71         ( ( r2_hidden @ D @ C ) <=>
% 0.53/0.71           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.53/0.71  thf('63', plain,
% 0.53/0.71      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.53/0.71         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.53/0.71          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.53/0.71          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.53/0.71      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.53/0.71  thf('64', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.53/0.71          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.53/0.71      inference('eq_fact', [status(thm)], ['63'])).
% 0.53/0.71  thf('65', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.53/0.71          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.53/0.71      inference('eq_fact', [status(thm)], ['63'])).
% 0.53/0.71  thf('66', plain,
% 0.53/0.71      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.53/0.71         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.53/0.71          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.53/0.71          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.53/0.71          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.53/0.71      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.53/0.71  thf('67', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.53/0.71          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.53/0.71          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.53/0.71          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['65', '66'])).
% 0.53/0.71  thf('68', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.53/0.71          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.53/0.71          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.53/0.71      inference('simplify', [status(thm)], ['67'])).
% 0.53/0.71  thf('69', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.53/0.71          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.53/0.71      inference('eq_fact', [status(thm)], ['63'])).
% 0.53/0.71  thf('70', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.53/0.71          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 0.53/0.71      inference('clc', [status(thm)], ['68', '69'])).
% 0.53/0.71  thf('71', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.53/0.71           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.71  thf('72', plain,
% 0.53/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.71             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.53/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.71                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.53/0.71      inference('split', [status(esa)], ['3'])).
% 0.53/0.71  thf('73', plain,
% 0.53/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.53/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.71                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.53/0.71      inference('sup+', [status(thm)], ['71', '72'])).
% 0.53/0.71  thf('74', plain,
% 0.53/0.71      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.53/0.71         (~ (r2_hidden @ X4 @ X3)
% 0.53/0.71          | ~ (r2_hidden @ X4 @ X2)
% 0.53/0.71          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.53/0.71      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.53/0.71  thf('75', plain,
% 0.53/0.71      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.53/0.71         (~ (r2_hidden @ X4 @ X2)
% 0.53/0.71          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.53/0.71      inference('simplify', [status(thm)], ['74'])).
% 0.53/0.71  thf('76', plain,
% 0.53/0.71      ((![X0 : $i]:
% 0.53/0.72          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.72           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.53/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.72                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.53/0.72      inference('sup-', [status(thm)], ['73', '75'])).
% 0.53/0.72  thf('77', plain,
% 0.53/0.72      ((![X0 : $i]:
% 0.53/0.72          (((X0) = (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.53/0.72           | ~ (r2_hidden @ (sk_D @ X0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B)))
% 0.53/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.72                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.53/0.72      inference('sup-', [status(thm)], ['70', '76'])).
% 0.53/0.72  thf('78', plain,
% 0.53/0.72      (((((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.53/0.72         | ((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.53/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.72                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.53/0.72      inference('sup-', [status(thm)], ['64', '77'])).
% 0.53/0.72  thf('79', plain,
% 0.53/0.72      ((((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.53/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.72                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.53/0.72      inference('simplify', [status(thm)], ['78'])).
% 0.53/0.72  thf('80', plain,
% 0.53/0.72      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.72          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.72             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.53/0.72       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.53/0.72      inference('split', [status(esa)], ['3'])).
% 0.53/0.72  thf('81', plain,
% 0.53/0.72      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.72          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.72             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.53/0.72      inference('sat_resolution*', [status(thm)], ['2', '38', '80'])).
% 0.53/0.72  thf('82', plain,
% 0.53/0.72      (((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.72      inference('simpl_trail', [status(thm)], ['79', '81'])).
% 0.53/0.72  thf('83', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.53/0.72      inference('demod', [status(thm)], ['58', '59', '62', '82'])).
% 0.53/0.72  thf('84', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.53/0.72      inference('demod', [status(thm)], ['55', '83'])).
% 0.53/0.72  thf('85', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.53/0.72      inference('simplify', [status(thm)], ['84'])).
% 0.53/0.72  thf('86', plain, ($false), inference('demod', [status(thm)], ['40', '85'])).
% 0.53/0.72  
% 0.53/0.72  % SZS output end Refutation
% 0.53/0.72  
% 0.53/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
