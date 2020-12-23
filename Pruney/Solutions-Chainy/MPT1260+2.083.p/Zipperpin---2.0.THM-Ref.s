%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B2o1Od7Olz

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 398 expanded)
%              Number of leaves         :   32 ( 122 expanded)
%              Depth                    :   20
%              Number of atoms          : 1483 (5697 expanded)
%              Number of equality atoms :   83 ( 265 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X29 )
      | ( ( k1_tops_1 @ X29 @ X30 )
        = X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('7',plain,
    ( ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
        | ~ ( v3_pre_topc @ X30 @ X29 )
        | ( ( k1_tops_1 @ X29 @ X30 )
          = X30 ) )
   <= ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
        | ~ ( v3_pre_topc @ X30 @ X29 )
        | ( ( k1_tops_1 @ X29 @ X30 )
          = X30 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) )
   <= ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
        | ~ ( v3_pre_topc @ X30 @ X29 )
        | ( ( k1_tops_1 @ X29 @ X30 )
          = X30 ) )
    | ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X29 )
      | ( ( k1_tops_1 @ X29 @ X30 )
        = X30 ) ) ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X29 )
      | ( ( k1_tops_1 @ X29 @ X30 )
        = X30 ) ) ),
    inference(simpl_trail,[status(thm)],['7','15'])).

thf('17',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k2_tops_1 @ X28 @ X27 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X28 ) @ ( k2_pre_topc @ X28 @ X27 ) @ ( k1_tops_1 @ X28 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('27',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24','31'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['20','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','38'])).

thf('40',plain,(
    ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k1_tops_1 @ X32 @ X31 )
       != X31 )
      | ( v3_pre_topc @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('43',plain,
    ( ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 )
        | ( ( k1_tops_1 @ X32 @ X31 )
         != X31 )
        | ( v3_pre_topc @ X31 @ X32 ) )
   <= ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 )
        | ( ( k1_tops_1 @ X32 @ X31 )
         != X31 )
        | ( v3_pre_topc @ X31 @ X32 ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) )
   <= ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 )
        | ( ( k1_tops_1 @ X32 @ X31 )
         != X31 )
        | ( v3_pre_topc @ X31 @ X32 ) )
    | ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('50',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( ( k1_tops_1 @ X32 @ X31 )
       != X31 )
      | ( v3_pre_topc @ X31 @ X32 ) ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( ( k1_tops_1 @ X32 @ X31 )
       != X31 )
      | ( v3_pre_topc @ X31 @ X32 ) ) ),
    inference(simpl_trail,[status(thm)],['43','50'])).

thf('52',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != sk_B_1 )
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
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != sk_B_1 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('57',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k1_tops_1 @ X34 @ X33 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 @ ( k2_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('64',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r1_tarski @ X25 @ ( k2_pre_topc @ X26 @ X25 ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('68',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('71',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('72',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('74',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('75',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('77',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('78',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('80',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['72','79'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('81',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X17 @ X15 )
        = ( k9_subset_1 @ X16 @ X17 @ ( k3_subset_1 @ X16 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
        | ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
          = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('84',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('85',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X10 @ ( k3_subset_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('86',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('88',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['83','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
        | ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
          = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['82','89'])).

thf('91',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('92',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','38','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
      | ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
        = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['90','92'])).

thf('94',plain,
    ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['69','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('96',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('98',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( sk_B @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('99',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( sk_B @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('102',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( sk_B @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','103'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('105',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X7 @ X6 @ X6 )
        = X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['94','97','106'])).

thf('108',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['58','59','62','107'])).

thf('109',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( sk_B_1 != sk_B_1 ) ),
    inference(demod,[status(thm)],['55','108'])).

thf('110',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['40','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B2o1Od7Olz
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 190 iterations in 0.092s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.54  thf(t76_tops_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.54             ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.54               ( k7_subset_1 @
% 0.21/0.54                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54              ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.54                ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.54                  ( k7_subset_1 @
% 0.21/0.54                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 0.21/0.54        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (~ ((v3_pre_topc @ sk_B_1 @ sk_A)) | 
% 0.21/0.54       ~
% 0.21/0.54       (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 0.21/0.54        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['3'])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t55_tops_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( l1_pre_topc @ B ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54               ( ![D:$i]:
% 0.21/0.54                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.54                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.21/0.54                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.21/0.54                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.21/0.54                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X29)
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54          | ~ (v3_pre_topc @ X30 @ X29)
% 0.21/0.54          | ((k1_tops_1 @ X29 @ X30) = (X30))
% 0.21/0.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54          | ~ (l1_pre_topc @ X32)
% 0.21/0.54          | ~ (v2_pre_topc @ X32))),
% 0.21/0.54      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      ((![X29 : $i, X30 : $i]:
% 0.21/0.54          (~ (l1_pre_topc @ X29)
% 0.21/0.54           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54           | ~ (v3_pre_topc @ X30 @ X29)
% 0.21/0.54           | ((k1_tops_1 @ X29 @ X30) = (X30))))
% 0.21/0.54         <= ((![X29 : $i, X30 : $i]:
% 0.21/0.54                (~ (l1_pre_topc @ X29)
% 0.21/0.54                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54                 | ~ (v3_pre_topc @ X30 @ X29)
% 0.21/0.54                 | ((k1_tops_1 @ X29 @ X30) = (X30)))))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      ((![X31 : $i, X32 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54           | ~ (l1_pre_topc @ X32)
% 0.21/0.54           | ~ (v2_pre_topc @ X32)))
% 0.21/0.54         <= ((![X31 : $i, X32 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54                 | ~ (l1_pre_topc @ X32)
% 0.21/0.54                 | ~ (v2_pre_topc @ X32))))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.54         <= ((![X31 : $i, X32 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54                 | ~ (l1_pre_topc @ X32)
% 0.21/0.54                 | ~ (v2_pre_topc @ X32))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (~
% 0.21/0.54       (![X31 : $i, X32 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54           | ~ (l1_pre_topc @ X32)
% 0.21/0.54           | ~ (v2_pre_topc @ X32)))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      ((![X29 : $i, X30 : $i]:
% 0.21/0.54          (~ (l1_pre_topc @ X29)
% 0.21/0.54           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54           | ~ (v3_pre_topc @ X30 @ X29)
% 0.21/0.54           | ((k1_tops_1 @ X29 @ X30) = (X30)))) | 
% 0.21/0.54       (![X31 : $i, X32 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54           | ~ (l1_pre_topc @ X32)
% 0.21/0.54           | ~ (v2_pre_topc @ X32)))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      ((![X29 : $i, X30 : $i]:
% 0.21/0.54          (~ (l1_pre_topc @ X29)
% 0.21/0.54           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54           | ~ (v3_pre_topc @ X30 @ X29)
% 0.21/0.54           | ((k1_tops_1 @ X29 @ X30) = (X30))))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X29 : $i, X30 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X29)
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54          | ~ (v3_pre_topc @ X30 @ X29)
% 0.21/0.54          | ((k1_tops_1 @ X29 @ X30) = (X30)))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['7', '15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1))
% 0.21/0.54        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '16'])).
% 0.21/0.54  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1))
% 0.21/0.54        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.21/0.54         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(l78_tops_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.54             ( k7_subset_1 @
% 0.21/0.54               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.21/0.54               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X27 : $i, X28 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.54          | ((k2_tops_1 @ X28 @ X27)
% 0.21/0.54              = (k7_subset_1 @ (u1_struct_0 @ X28) @ 
% 0.21/0.54                 (k2_pre_topc @ X28 @ X27) @ (k1_tops_1 @ X28 @ X27)))
% 0.21/0.54          | ~ (l1_pre_topc @ X28))),
% 0.21/0.54      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.54  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k2_pre_topc, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @
% 0.21/0.54         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X23 : $i, X24 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X23)
% 0.21/0.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.54          | (m1_subset_1 @ (k2_pre_topc @ X23 @ X24) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.21/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.54  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.21/0.54          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 0.21/0.54           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.21/0.54            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['23', '24', '31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.21/0.54         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['20', '32'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 0.21/0.54           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 0.21/0.54             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['33', '36'])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 0.21/0.54       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.54  thf('39', plain, (~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['2', '38'])).
% 0.21/0.54  thf('40', plain, (~ (v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X29)
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54          | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.21/0.54          | (v3_pre_topc @ X31 @ X32)
% 0.21/0.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54          | ~ (l1_pre_topc @ X32)
% 0.21/0.54          | ~ (v2_pre_topc @ X32))),
% 0.21/0.54      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      ((![X31 : $i, X32 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54           | ~ (l1_pre_topc @ X32)
% 0.21/0.54           | ~ (v2_pre_topc @ X32)
% 0.21/0.54           | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.21/0.54           | (v3_pre_topc @ X31 @ X32)))
% 0.21/0.54         <= ((![X31 : $i, X32 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54                 | ~ (l1_pre_topc @ X32)
% 0.21/0.54                 | ~ (v2_pre_topc @ X32)
% 0.21/0.54                 | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.21/0.54                 | (v3_pre_topc @ X31 @ X32))))),
% 0.21/0.54      inference('split', [status(esa)], ['42'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      ((![X29 : $i, X30 : $i]:
% 0.21/0.54          (~ (l1_pre_topc @ X29)
% 0.21/0.54           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))))
% 0.21/0.54         <= ((![X29 : $i, X30 : $i]:
% 0.21/0.54                (~ (l1_pre_topc @ X29)
% 0.21/0.54                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29))))))),
% 0.21/0.54      inference('split', [status(esa)], ['42'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A))
% 0.21/0.54         <= ((![X29 : $i, X30 : $i]:
% 0.21/0.54                (~ (l1_pre_topc @ X29)
% 0.21/0.54                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29))))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.54  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (~
% 0.21/0.54       (![X29 : $i, X30 : $i]:
% 0.21/0.54          (~ (l1_pre_topc @ X29)
% 0.21/0.54           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))))),
% 0.21/0.54      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      ((![X31 : $i, X32 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54           | ~ (l1_pre_topc @ X32)
% 0.21/0.54           | ~ (v2_pre_topc @ X32)
% 0.21/0.54           | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.21/0.54           | (v3_pre_topc @ X31 @ X32))) | 
% 0.21/0.54       (![X29 : $i, X30 : $i]:
% 0.21/0.54          (~ (l1_pre_topc @ X29)
% 0.21/0.54           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))))),
% 0.21/0.54      inference('split', [status(esa)], ['42'])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      ((![X31 : $i, X32 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54           | ~ (l1_pre_topc @ X32)
% 0.21/0.54           | ~ (v2_pre_topc @ X32)
% 0.21/0.54           | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.21/0.54           | (v3_pre_topc @ X31 @ X32)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X31 : $i, X32 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54          | ~ (l1_pre_topc @ X32)
% 0.21/0.54          | ~ (v2_pre_topc @ X32)
% 0.21/0.54          | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.21/0.54          | (v3_pre_topc @ X31 @ X32))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['43', '50'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.54        | ((k1_tops_1 @ sk_A @ sk_B_1) != (sk_B_1))
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['41', '51'])).
% 0.21/0.54  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.54        | ((k1_tops_1 @ sk_A @ sk_B_1) != (sk_B_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t74_tops_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( k1_tops_1 @ A @ B ) =
% 0.21/0.54             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (![X33 : $i, X34 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.21/0.54          | ((k1_tops_1 @ X34 @ X33)
% 0.21/0.54              = (k7_subset_1 @ (u1_struct_0 @ X34) @ X33 @ 
% 0.21/0.54                 (k2_tops_1 @ X34 @ X33)))
% 0.21/0.54          | ~ (l1_pre_topc @ X34))),
% 0.21/0.54      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.21/0.54               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.54  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.21/0.54          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 0.21/0.54           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t48_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      (![X25 : $i, X26 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.54          | (r1_tarski @ X25 @ (k2_pre_topc @ X26 @ X25))
% 0.21/0.54          | ~ (l1_pre_topc @ X26))),
% 0.21/0.54      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.54  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('67', plain, ((r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      (![X20 : $i, X22 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 0.21/0.54           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf('71', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.21/0.54      inference('split', [status(esa)], ['3'])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['70', '71'])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.54  thf(dt_k3_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.21/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.54  thf('75', plain,
% 0.21/0.54      ((m1_subset_1 @ (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.54  thf(d5_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.54  thf('77', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i]:
% 0.21/0.54         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.21/0.54          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 0.21/0.54         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.54  thf('79', plain,
% 0.21/0.54      ((m1_subset_1 @ (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['75', '78'])).
% 0.21/0.54  thf('80', plain,
% 0.21/0.54      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.54         (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1))))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['72', '79'])).
% 0.21/0.54  thf(t32_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.21/0.54             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.21/0.54  thf('81', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.21/0.54          | ((k7_subset_1 @ X16 @ X17 @ X15)
% 0.21/0.54              = (k9_subset_1 @ X16 @ X17 @ (k3_subset_1 @ X16 @ X15)))
% 0.21/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.21/0.54  thf('82', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))
% 0.21/0.54           | ((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0 @ 
% 0.21/0.54               (k2_tops_1 @ sk_A @ sk_B_1))
% 0.21/0.54               = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0 @ 
% 0.21/0.54                  (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.21/0.54                   (k2_tops_1 @ sk_A @ sk_B_1))))))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['80', '81'])).
% 0.21/0.54  thf('83', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['70', '71'])).
% 0.21/0.54  thf('84', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.54  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.54  thf('85', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         (((k3_subset_1 @ X10 @ (k3_subset_1 @ X10 @ X9)) = (X9))
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.54      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.54  thf('86', plain,
% 0.21/0.54      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.21/0.54         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.54  thf('87', plain,
% 0.21/0.54      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 0.21/0.54         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.54  thf('88', plain,
% 0.21/0.54      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.21/0.54         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.54  thf('89', plain,
% 0.21/0.54      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.21/0.54          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['83', '88'])).
% 0.21/0.54  thf('90', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))
% 0.21/0.54           | ((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0 @ 
% 0.21/0.54               (k2_tops_1 @ sk_A @ sk_B_1))
% 0.21/0.54               = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0 @ sk_B_1))))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.21/0.54      inference('demod', [status(thm)], ['82', '89'])).
% 0.21/0.54  thf('91', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 0.21/0.54       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('split', [status(esa)], ['3'])).
% 0.21/0.54  thf('92', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.21/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['2', '38', '91'])).
% 0.21/0.54  thf('93', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))
% 0.21/0.54          | ((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0 @ 
% 0.21/0.54              (k2_tops_1 @ sk_A @ sk_B_1))
% 0.21/0.54              = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0 @ sk_B_1)))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['90', '92'])).
% 0.21/0.54  thf('94', plain,
% 0.21/0.54      (((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1 @ 
% 0.21/0.54         (k2_tops_1 @ sk_A @ sk_B_1))
% 0.21/0.54         = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['69', '93'])).
% 0.21/0.54  thf('95', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.54  thf('96', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.21/0.54          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.54  thf('97', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1 @ X0)
% 0.21/0.54           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.54  thf(rc2_subset_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ?[B:$i]:
% 0.21/0.54       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.54  thf('98', plain,
% 0.21/0.54      (![X11 : $i]: (m1_subset_1 @ (sk_B @ X11) @ (k1_zfmisc_1 @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.21/0.54  thf('99', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.21/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.54  thf('100', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (m1_subset_1 @ (k3_subset_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['98', '99'])).
% 0.21/0.54  thf('101', plain,
% 0.21/0.54      (![X11 : $i]: (m1_subset_1 @ (sk_B @ X11) @ (k1_zfmisc_1 @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.21/0.54  thf('102', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i]:
% 0.21/0.54         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.21/0.54          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.54  thf('103', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k3_subset_1 @ X0 @ (sk_B @ X0)) = (k4_xboole_0 @ X0 @ (sk_B @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['101', '102'])).
% 0.21/0.54  thf('104', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (m1_subset_1 @ (k4_xboole_0 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['100', '103'])).
% 0.21/0.54  thf(idempotence_k9_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.21/0.54  thf('105', plain,
% 0.21/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.54         (((k9_subset_1 @ X7 @ X6 @ X6) = (X6))
% 0.21/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.54      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.21/0.54  thf('106', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.54  thf('107', plain,
% 0.21/0.54      (((k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['94', '97', '106'])).
% 0.21/0.54  thf('108', plain, (((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['58', '59', '62', '107'])).
% 0.21/0.54  thf('109', plain, (((v3_pre_topc @ sk_B_1 @ sk_A) | ((sk_B_1) != (sk_B_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['55', '108'])).
% 0.21/0.54  thf('110', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('simplify', [status(thm)], ['109'])).
% 0.21/0.54  thf('111', plain, ($false), inference('demod', [status(thm)], ['40', '110'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
