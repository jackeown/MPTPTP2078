%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tlLZb61FkB

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 309 expanded)
%              Number of leaves         :   29 (  96 expanded)
%              Depth                    :   21
%              Number of atoms          : 1250 (4387 expanded)
%              Number of equality atoms :   92 ( 245 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X22 )
        = X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('7',plain,
    ( ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( v3_pre_topc @ X22 @ X21 )
        | ( ( k1_tops_1 @ X21 @ X22 )
          = X22 ) )
   <= ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( v3_pre_topc @ X22 @ X21 )
        | ( ( k1_tops_1 @ X21 @ X22 )
          = X22 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) )
   <= ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( v3_pre_topc @ X22 @ X21 )
        | ( ( k1_tops_1 @ X21 @ X22 )
          = X22 ) )
    | ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X22 )
        = X22 ) ) ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X22 )
        = X22 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_tops_1 @ X20 @ X19 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k2_pre_topc @ X20 @ X19 ) @ ( k1_tops_1 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k1_tops_1 @ X24 @ X23 )
       != X23 )
      | ( v3_pre_topc @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('43',plain,
    ( ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 )
        | ( ( k1_tops_1 @ X24 @ X23 )
         != X23 )
        | ( v3_pre_topc @ X23 @ X24 ) )
   <= ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 )
        | ( ( k1_tops_1 @ X24 @ X23 )
         != X23 )
        | ( v3_pre_topc @ X23 @ X24 ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
   <= ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 )
        | ( ( k1_tops_1 @ X24 @ X23 )
         != X23 )
        | ( v3_pre_topc @ X23 @ X24 ) )
    | ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('50',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( ( k1_tops_1 @ X24 @ X23 )
       != X23 )
      | ( v3_pre_topc @ X23 @ X24 ) ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( ( k1_tops_1 @ X24 @ X23 )
       != X23 )
      | ( v3_pre_topc @ X23 @ X24 ) ) ),
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

thf('56',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('60',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','38','59'])).

thf('61',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['58','60'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('63',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('64',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('67',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('70',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('76',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','78'])).

thf('80',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['61','81'])).

thf('83',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('84',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('90',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('92',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k1_tops_1 @ X26 @ X25 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 @ ( k2_tops_1 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94','97'])).

thf('99',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['90','98'])).

thf('100',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['55','99'])).

thf('101',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['40','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tlLZb61FkB
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:00:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 272 iterations in 0.102s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.20/0.55  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(t76_tops_1, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.55             ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.55               ( k7_subset_1 @
% 0.20/0.55                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55              ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.55                ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.55                  ( k7_subset_1 @
% 0.20/0.55                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.20/0.55        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.20/0.55       ~
% 0.20/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.20/0.55        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['3'])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t55_tops_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( l1_pre_topc @ B ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.55                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.20/0.55                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.20/0.55                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.20/0.55                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X21)
% 0.20/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.55          | ~ (v3_pre_topc @ X22 @ X21)
% 0.20/0.55          | ((k1_tops_1 @ X21 @ X22) = (X22))
% 0.20/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.55          | ~ (l1_pre_topc @ X24)
% 0.20/0.55          | ~ (v2_pre_topc @ X24))),
% 0.20/0.55      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      ((![X21 : $i, X22 : $i]:
% 0.20/0.55          (~ (l1_pre_topc @ X21)
% 0.20/0.55           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.55           | ~ (v3_pre_topc @ X22 @ X21)
% 0.20/0.55           | ((k1_tops_1 @ X21 @ X22) = (X22))))
% 0.20/0.55         <= ((![X21 : $i, X22 : $i]:
% 0.20/0.55                (~ (l1_pre_topc @ X21)
% 0.20/0.55                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.55                 | ~ (v3_pre_topc @ X22 @ X21)
% 0.20/0.55                 | ((k1_tops_1 @ X21 @ X22) = (X22)))))),
% 0.20/0.55      inference('split', [status(esa)], ['6'])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      ((![X23 : $i, X24 : $i]:
% 0.20/0.55          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.55           | ~ (l1_pre_topc @ X24)
% 0.20/0.55           | ~ (v2_pre_topc @ X24)))
% 0.20/0.55         <= ((![X23 : $i, X24 : $i]:
% 0.20/0.55                (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.55                 | ~ (l1_pre_topc @ X24)
% 0.20/0.55                 | ~ (v2_pre_topc @ X24))))),
% 0.20/0.55      inference('split', [status(esa)], ['6'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.20/0.55         <= ((![X23 : $i, X24 : $i]:
% 0.20/0.55                (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.55                 | ~ (l1_pre_topc @ X24)
% 0.20/0.55                 | ~ (v2_pre_topc @ X24))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (~
% 0.20/0.55       (![X23 : $i, X24 : $i]:
% 0.20/0.55          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.55           | ~ (l1_pre_topc @ X24)
% 0.20/0.55           | ~ (v2_pre_topc @ X24)))),
% 0.20/0.55      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      ((![X21 : $i, X22 : $i]:
% 0.20/0.55          (~ (l1_pre_topc @ X21)
% 0.20/0.55           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.55           | ~ (v3_pre_topc @ X22 @ X21)
% 0.20/0.55           | ((k1_tops_1 @ X21 @ X22) = (X22)))) | 
% 0.20/0.55       (![X23 : $i, X24 : $i]:
% 0.20/0.55          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.55           | ~ (l1_pre_topc @ X24)
% 0.20/0.55           | ~ (v2_pre_topc @ X24)))),
% 0.20/0.55      inference('split', [status(esa)], ['6'])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      ((![X21 : $i, X22 : $i]:
% 0.20/0.55          (~ (l1_pre_topc @ X21)
% 0.20/0.55           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.55           | ~ (v3_pre_topc @ X22 @ X21)
% 0.20/0.55           | ((k1_tops_1 @ X21 @ X22) = (X22))))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X21 : $i, X22 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X21)
% 0.20/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.55          | ~ (v3_pre_topc @ X22 @ X21)
% 0.20/0.55          | ((k1_tops_1 @ X21 @ X22) = (X22)))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['7', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.20/0.55        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['5', '16'])).
% 0.20/0.55  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.55         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '19'])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(l78_tops_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.55             ( k7_subset_1 @
% 0.20/0.55               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.20/0.55               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.55          | ((k2_tops_1 @ X20 @ X19)
% 0.20/0.55              = (k7_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.20/0.55                 (k2_pre_topc @ X20 @ X19) @ (k1_tops_1 @ X20 @ X19)))
% 0.20/0.55          | ~ (l1_pre_topc @ X20))),
% 0.20/0.55      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.55  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_k2_pre_topc, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.55       ( m1_subset_1 @
% 0.20/0.55         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X17)
% 0.20/0.55          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.55          | (m1_subset_1 @ (k2_pre_topc @ X17 @ X18) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.55  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.55  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.20/0.55          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.55           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.55            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['23', '24', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.20/0.55         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['20', '32'])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.55           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.20/0.55             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '36'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.20/0.55       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.55  thf('39', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['2', '38'])).
% 0.20/0.55  thf('40', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X21)
% 0.20/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.55          | ((k1_tops_1 @ X24 @ X23) != (X23))
% 0.20/0.55          | (v3_pre_topc @ X23 @ X24)
% 0.20/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.55          | ~ (l1_pre_topc @ X24)
% 0.20/0.55          | ~ (v2_pre_topc @ X24))),
% 0.20/0.55      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      ((![X23 : $i, X24 : $i]:
% 0.20/0.55          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.55           | ~ (l1_pre_topc @ X24)
% 0.20/0.55           | ~ (v2_pre_topc @ X24)
% 0.20/0.55           | ((k1_tops_1 @ X24 @ X23) != (X23))
% 0.20/0.55           | (v3_pre_topc @ X23 @ X24)))
% 0.20/0.55         <= ((![X23 : $i, X24 : $i]:
% 0.20/0.55                (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.55                 | ~ (l1_pre_topc @ X24)
% 0.20/0.55                 | ~ (v2_pre_topc @ X24)
% 0.20/0.55                 | ((k1_tops_1 @ X24 @ X23) != (X23))
% 0.20/0.55                 | (v3_pre_topc @ X23 @ X24))))),
% 0.20/0.55      inference('split', [status(esa)], ['42'])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((![X21 : $i, X22 : $i]:
% 0.20/0.55          (~ (l1_pre_topc @ X21)
% 0.20/0.55           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))))
% 0.20/0.55         <= ((![X21 : $i, X22 : $i]:
% 0.20/0.55                (~ (l1_pre_topc @ X21)
% 0.20/0.55                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))))),
% 0.20/0.55      inference('split', [status(esa)], ['42'])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_A))
% 0.20/0.55         <= ((![X21 : $i, X22 : $i]:
% 0.20/0.55                (~ (l1_pre_topc @ X21)
% 0.20/0.55                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.55  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (~
% 0.20/0.55       (![X21 : $i, X22 : $i]:
% 0.20/0.55          (~ (l1_pre_topc @ X21)
% 0.20/0.55           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))))),
% 0.20/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      ((![X23 : $i, X24 : $i]:
% 0.20/0.55          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.55           | ~ (l1_pre_topc @ X24)
% 0.20/0.55           | ~ (v2_pre_topc @ X24)
% 0.20/0.55           | ((k1_tops_1 @ X24 @ X23) != (X23))
% 0.20/0.55           | (v3_pre_topc @ X23 @ X24))) | 
% 0.20/0.55       (![X21 : $i, X22 : $i]:
% 0.20/0.55          (~ (l1_pre_topc @ X21)
% 0.20/0.55           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))))),
% 0.20/0.55      inference('split', [status(esa)], ['42'])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      ((![X23 : $i, X24 : $i]:
% 0.20/0.55          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.55           | ~ (l1_pre_topc @ X24)
% 0.20/0.55           | ~ (v2_pre_topc @ X24)
% 0.20/0.55           | ((k1_tops_1 @ X24 @ X23) != (X23))
% 0.20/0.55           | (v3_pre_topc @ X23 @ X24)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (![X23 : $i, X24 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.55          | ~ (l1_pre_topc @ X24)
% 0.20/0.55          | ~ (v2_pre_topc @ X24)
% 0.20/0.55          | ((k1_tops_1 @ X24 @ X23) != (X23))
% 0.20/0.55          | (v3_pre_topc @ X23 @ X24))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['43', '50'])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (((v3_pre_topc @ sk_B @ sk_A)
% 0.20/0.55        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 0.20/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['41', '51'])).
% 0.20/0.55  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.20/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.20/0.55      inference('split', [status(esa)], ['3'])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.55           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.20/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.20/0.55       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('split', [status(esa)], ['3'])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['2', '38', '59'])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['58', '60'])).
% 0.20/0.55  thf(t48_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.20/0.55           = (k3_xboole_0 @ X7 @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.55  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.55  thf('63', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.55  thf(t49_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.20/0.55       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.55         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 0.20/0.55           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.55           = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['63', '64'])).
% 0.20/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.55  thf(t100_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X3 @ X4)
% 0.20/0.55           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['66', '67'])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.20/0.55           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['65', '68'])).
% 0.20/0.55  thf(t3_boole, axiom,
% 0.20/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.55  thf('70', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.20/0.55           = (k3_xboole_0 @ X7 @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['70', '71'])).
% 0.20/0.55  thf('73', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X3 @ X4)
% 0.20/0.55           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.55  thf('75', plain,
% 0.20/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['73', '74'])).
% 0.20/0.55  thf(t2_boole, axiom,
% 0.20/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.55  thf('77', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['72', '75', '76'])).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['69', '77'])).
% 0.20/0.55  thf('79', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['62', '78'])).
% 0.20/0.55  thf('80', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.55         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 0.20/0.55           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.55  thf('82', plain,
% 0.20/0.55      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['61', '81'])).
% 0.20/0.55  thf('83', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.20/0.55           = (k3_xboole_0 @ X7 @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.55  thf('84', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.20/0.55           = (k3_xboole_0 @ X7 @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.55  thf('85', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.55           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['83', '84'])).
% 0.20/0.55  thf('86', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.55           = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['63', '64'])).
% 0.20/0.55  thf('87', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.55           = (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['85', '86'])).
% 0.20/0.55  thf('88', plain,
% 0.20/0.55      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 0.20/0.55         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['82', '87'])).
% 0.20/0.55  thf('89', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.55  thf('90', plain,
% 0.20/0.55      (((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.55  thf('91', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t74_tops_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ( k1_tops_1 @ A @ B ) =
% 0.20/0.55             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.55  thf('92', plain,
% 0.20/0.55      (![X25 : $i, X26 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.55          | ((k1_tops_1 @ X26 @ X25)
% 0.20/0.55              = (k7_subset_1 @ (u1_struct_0 @ X26) @ X25 @ 
% 0.20/0.55                 (k2_tops_1 @ X26 @ X25)))
% 0.20/0.55          | ~ (l1_pre_topc @ X26))),
% 0.20/0.55      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.20/0.55  thf('93', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.20/0.55            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.55  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('95', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('96', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.20/0.55          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.55  thf('97', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['95', '96'])).
% 0.20/0.55  thf('98', plain,
% 0.20/0.55      (((k1_tops_1 @ sk_A @ sk_B)
% 0.20/0.55         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['93', '94', '97'])).
% 0.20/0.55  thf('99', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['90', '98'])).
% 0.20/0.55  thf('100', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['55', '99'])).
% 0.20/0.55  thf('101', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.20/0.55      inference('simplify', [status(thm)], ['100'])).
% 0.20/0.55  thf('102', plain, ($false), inference('demod', [status(thm)], ['40', '101'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
