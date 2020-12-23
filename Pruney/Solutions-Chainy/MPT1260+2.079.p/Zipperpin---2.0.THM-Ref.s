%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HWx7rHgUJh

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 316 expanded)
%              Number of leaves         :   29 (  97 expanded)
%              Depth                    :   18
%              Number of atoms          : 1294 (4518 expanded)
%              Number of equality atoms :   87 ( 245 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X25 )
      | ( ( k1_tops_1 @ X25 @ X26 )
        = X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('7',plain,
    ( ! [X25: $i,X26: $i] :
        ( ~ ( l1_pre_topc @ X25 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
        | ~ ( v3_pre_topc @ X26 @ X25 )
        | ( ( k1_tops_1 @ X25 @ X26 )
          = X26 ) )
   <= ! [X25: $i,X26: $i] :
        ( ~ ( l1_pre_topc @ X25 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
        | ~ ( v3_pre_topc @ X26 @ X25 )
        | ( ( k1_tops_1 @ X25 @ X26 )
          = X26 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X27: $i,X28: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( l1_pre_topc @ X28 )
        | ~ ( v2_pre_topc @ X28 ) )
   <= ! [X27: $i,X28: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( l1_pre_topc @ X28 )
        | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X27: $i,X28: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( l1_pre_topc @ X28 )
        | ~ ( v2_pre_topc @ X28 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ! [X27: $i,X28: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( l1_pre_topc @ X28 )
        | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ! [X25: $i,X26: $i] :
        ( ~ ( l1_pre_topc @ X25 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
        | ~ ( v3_pre_topc @ X26 @ X25 )
        | ( ( k1_tops_1 @ X25 @ X26 )
          = X26 ) )
    | ! [X27: $i,X28: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( l1_pre_topc @ X28 )
        | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X25 )
      | ( ( k1_tops_1 @ X25 @ X26 )
        = X26 ) ) ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X25 )
      | ( ( k1_tops_1 @ X25 @ X26 )
        = X26 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k1_tops_1 @ X28 @ X27 )
       != X27 )
      | ( v3_pre_topc @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('43',plain,
    ( ! [X27: $i,X28: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( l1_pre_topc @ X28 )
        | ~ ( v2_pre_topc @ X28 )
        | ( ( k1_tops_1 @ X28 @ X27 )
         != X27 )
        | ( v3_pre_topc @ X27 @ X28 ) )
   <= ! [X27: $i,X28: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( l1_pre_topc @ X28 )
        | ~ ( v2_pre_topc @ X28 )
        | ( ( k1_tops_1 @ X28 @ X27 )
         != X27 )
        | ( v3_pre_topc @ X27 @ X28 ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ! [X25: $i,X26: $i] :
        ( ~ ( l1_pre_topc @ X25 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) )
   <= ! [X25: $i,X26: $i] :
        ( ~ ( l1_pre_topc @ X25 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X25: $i,X26: $i] :
        ( ~ ( l1_pre_topc @ X25 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ! [X25: $i,X26: $i] :
        ( ~ ( l1_pre_topc @ X25 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X27: $i,X28: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( l1_pre_topc @ X28 )
        | ~ ( v2_pre_topc @ X28 )
        | ( ( k1_tops_1 @ X28 @ X27 )
         != X27 )
        | ( v3_pre_topc @ X27 @ X28 ) )
    | ! [X25: $i,X26: $i] :
        ( ~ ( l1_pre_topc @ X25 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('50',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( ( k1_tops_1 @ X28 @ X27 )
       != X27 )
      | ( v3_pre_topc @ X27 @ X28 ) ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( ( k1_tops_1 @ X28 @ X27 )
       != X27 )
      | ( v3_pre_topc @ X27 @ X28 ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k1_tops_1 @ X30 @ X29 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ ( k2_tops_1 @ X30 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('64',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('65',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('66',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('67',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('68',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('69',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('73',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('76',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('79',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('80',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf('82',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X3 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X3 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['65','85'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('87',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('88',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('90',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','93'])).

thf('95',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('96',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','38','95'])).

thf('97',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['94','96'])).

thf('98',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['58','59','62','97'])).

thf('99',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['55','98'])).

thf('100',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['40','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HWx7rHgUJh
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:06:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.19/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.58  % Solved by: fo/fo7.sh
% 0.19/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.58  % done 248 iterations in 0.144s
% 0.19/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.58  % SZS output start Refutation
% 0.19/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.58  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.19/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.58  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.58  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.19/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.58  thf(t76_tops_1, conjecture,
% 0.19/0.58    (![A:$i]:
% 0.19/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.58       ( ![B:$i]:
% 0.19/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.58           ( ( v3_pre_topc @ B @ A ) <=>
% 0.19/0.58             ( ( k2_tops_1 @ A @ B ) =
% 0.19/0.58               ( k7_subset_1 @
% 0.19/0.58                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.19/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.58    (~( ![A:$i]:
% 0.19/0.58        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.58          ( ![B:$i]:
% 0.19/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.58              ( ( v3_pre_topc @ B @ A ) <=>
% 0.19/0.58                ( ( k2_tops_1 @ A @ B ) =
% 0.19/0.58                  ( k7_subset_1 @
% 0.19/0.58                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.19/0.58    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.19/0.58  thf('0', plain,
% 0.19/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.19/0.58        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('1', plain,
% 0.19/0.58      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.19/0.58      inference('split', [status(esa)], ['0'])).
% 0.19/0.58  thf('2', plain,
% 0.19/0.58      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.19/0.58       ~
% 0.19/0.58       (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.19/0.58      inference('split', [status(esa)], ['0'])).
% 0.19/0.58  thf('3', plain,
% 0.19/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.19/0.58        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('4', plain,
% 0.19/0.58      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.19/0.58      inference('split', [status(esa)], ['3'])).
% 0.19/0.58  thf('5', plain,
% 0.19/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf(t55_tops_1, axiom,
% 0.19/0.58    (![A:$i]:
% 0.19/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.58       ( ![B:$i]:
% 0.19/0.58         ( ( l1_pre_topc @ B ) =>
% 0.19/0.58           ( ![C:$i]:
% 0.19/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.58               ( ![D:$i]:
% 0.19/0.58                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.58                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.19/0.58                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.19/0.58                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.19/0.58                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.58  thf('6', plain,
% 0.19/0.58      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.58         (~ (l1_pre_topc @ X25)
% 0.19/0.58          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.19/0.58          | ~ (v3_pre_topc @ X26 @ X25)
% 0.19/0.58          | ((k1_tops_1 @ X25 @ X26) = (X26))
% 0.19/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.58          | ~ (l1_pre_topc @ X28)
% 0.19/0.58          | ~ (v2_pre_topc @ X28))),
% 0.19/0.58      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.19/0.58  thf('7', plain,
% 0.19/0.58      ((![X25 : $i, X26 : $i]:
% 0.19/0.58          (~ (l1_pre_topc @ X25)
% 0.19/0.58           | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.19/0.58           | ~ (v3_pre_topc @ X26 @ X25)
% 0.19/0.58           | ((k1_tops_1 @ X25 @ X26) = (X26))))
% 0.19/0.58         <= ((![X25 : $i, X26 : $i]:
% 0.19/0.58                (~ (l1_pre_topc @ X25)
% 0.19/0.58                 | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.19/0.58                 | ~ (v3_pre_topc @ X26 @ X25)
% 0.19/0.58                 | ((k1_tops_1 @ X25 @ X26) = (X26)))))),
% 0.19/0.58      inference('split', [status(esa)], ['6'])).
% 0.19/0.58  thf('8', plain,
% 0.19/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('9', plain,
% 0.19/0.58      ((![X27 : $i, X28 : $i]:
% 0.19/0.58          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.58           | ~ (l1_pre_topc @ X28)
% 0.19/0.58           | ~ (v2_pre_topc @ X28)))
% 0.19/0.58         <= ((![X27 : $i, X28 : $i]:
% 0.19/0.58                (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.58                 | ~ (l1_pre_topc @ X28)
% 0.19/0.58                 | ~ (v2_pre_topc @ X28))))),
% 0.19/0.58      inference('split', [status(esa)], ['6'])).
% 0.19/0.58  thf('10', plain,
% 0.19/0.58      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.19/0.58         <= ((![X27 : $i, X28 : $i]:
% 0.19/0.58                (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.58                 | ~ (l1_pre_topc @ X28)
% 0.19/0.58                 | ~ (v2_pre_topc @ X28))))),
% 0.19/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.58  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('13', plain,
% 0.19/0.58      (~
% 0.19/0.58       (![X27 : $i, X28 : $i]:
% 0.19/0.58          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.58           | ~ (l1_pre_topc @ X28)
% 0.19/0.58           | ~ (v2_pre_topc @ X28)))),
% 0.19/0.58      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.19/0.58  thf('14', plain,
% 0.19/0.58      ((![X25 : $i, X26 : $i]:
% 0.19/0.58          (~ (l1_pre_topc @ X25)
% 0.19/0.58           | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.19/0.58           | ~ (v3_pre_topc @ X26 @ X25)
% 0.19/0.58           | ((k1_tops_1 @ X25 @ X26) = (X26)))) | 
% 0.19/0.58       (![X27 : $i, X28 : $i]:
% 0.19/0.58          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.58           | ~ (l1_pre_topc @ X28)
% 0.19/0.58           | ~ (v2_pre_topc @ X28)))),
% 0.19/0.58      inference('split', [status(esa)], ['6'])).
% 0.19/0.58  thf('15', plain,
% 0.19/0.58      ((![X25 : $i, X26 : $i]:
% 0.19/0.58          (~ (l1_pre_topc @ X25)
% 0.19/0.58           | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.19/0.58           | ~ (v3_pre_topc @ X26 @ X25)
% 0.19/0.58           | ((k1_tops_1 @ X25 @ X26) = (X26))))),
% 0.19/0.58      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 0.19/0.58  thf('16', plain,
% 0.19/0.58      (![X25 : $i, X26 : $i]:
% 0.19/0.58         (~ (l1_pre_topc @ X25)
% 0.19/0.58          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.19/0.58          | ~ (v3_pre_topc @ X26 @ X25)
% 0.19/0.58          | ((k1_tops_1 @ X25 @ X26) = (X26)))),
% 0.19/0.58      inference('simpl_trail', [status(thm)], ['7', '15'])).
% 0.19/0.58  thf('17', plain,
% 0.19/0.58      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.19/0.58        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.19/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.58      inference('sup-', [status(thm)], ['5', '16'])).
% 0.19/0.58  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('19', plain,
% 0.19/0.58      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.19/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.58  thf('20', plain,
% 0.19/0.58      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.19/0.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['4', '19'])).
% 0.19/0.58  thf('21', plain,
% 0.19/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf(l78_tops_1, axiom,
% 0.19/0.58    (![A:$i]:
% 0.19/0.58     ( ( l1_pre_topc @ A ) =>
% 0.19/0.58       ( ![B:$i]:
% 0.19/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.58           ( ( k2_tops_1 @ A @ B ) =
% 0.19/0.58             ( k7_subset_1 @
% 0.19/0.58               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.19/0.58               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.58  thf('22', plain,
% 0.19/0.58      (![X23 : $i, X24 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.19/0.58          | ((k2_tops_1 @ X24 @ X23)
% 0.19/0.58              = (k7_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.19/0.58                 (k2_pre_topc @ X24 @ X23) @ (k1_tops_1 @ X24 @ X23)))
% 0.19/0.58          | ~ (l1_pre_topc @ X24))),
% 0.19/0.58      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.19/0.58  thf('23', plain,
% 0.19/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.58        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.58  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('25', plain,
% 0.19/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf(dt_k2_pre_topc, axiom,
% 0.19/0.58    (![A:$i,B:$i]:
% 0.19/0.58     ( ( ( l1_pre_topc @ A ) & 
% 0.19/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.58       ( m1_subset_1 @
% 0.19/0.58         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.58  thf('26', plain,
% 0.19/0.58      (![X21 : $i, X22 : $i]:
% 0.19/0.58         (~ (l1_pre_topc @ X21)
% 0.19/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.19/0.58          | (m1_subset_1 @ (k2_pre_topc @ X21 @ X22) @ 
% 0.19/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 0.19/0.58      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.19/0.58  thf('27', plain,
% 0.19/0.58      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.19/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.58  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('29', plain,
% 0.19/0.58      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.19/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.58  thf(redefinition_k7_subset_1, axiom,
% 0.19/0.58    (![A:$i,B:$i,C:$i]:
% 0.19/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.58       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.19/0.58  thf('30', plain,
% 0.19/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.19/0.58          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.19/0.58      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.19/0.58  thf('31', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.19/0.58           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.19/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.58  thf('32', plain,
% 0.19/0.58      (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.19/0.58            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.58      inference('demod', [status(thm)], ['23', '24', '31'])).
% 0.19/0.58  thf('33', plain,
% 0.19/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.19/0.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.19/0.58      inference('sup+', [status(thm)], ['20', '32'])).
% 0.19/0.58  thf('34', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.19/0.58           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.19/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.58  thf('35', plain,
% 0.19/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.19/0.58         <= (~
% 0.19/0.58             (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.19/0.58      inference('split', [status(esa)], ['0'])).
% 0.19/0.58  thf('36', plain,
% 0.19/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.19/0.58         <= (~
% 0.19/0.58             (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.19/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.58  thf('37', plain,
% 0.19/0.58      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.19/0.58         <= (~
% 0.19/0.58             (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.19/0.58             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['33', '36'])).
% 0.19/0.58  thf('38', plain,
% 0.19/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.19/0.58       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.19/0.58      inference('simplify', [status(thm)], ['37'])).
% 0.19/0.58  thf('39', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.19/0.58      inference('sat_resolution*', [status(thm)], ['2', '38'])).
% 0.19/0.58  thf('40', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.19/0.58      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 0.19/0.58  thf('41', plain,
% 0.19/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('42', plain,
% 0.19/0.58      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.58         (~ (l1_pre_topc @ X25)
% 0.19/0.58          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.19/0.58          | ((k1_tops_1 @ X28 @ X27) != (X27))
% 0.19/0.58          | (v3_pre_topc @ X27 @ X28)
% 0.19/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.58          | ~ (l1_pre_topc @ X28)
% 0.19/0.58          | ~ (v2_pre_topc @ X28))),
% 0.19/0.58      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.19/0.58  thf('43', plain,
% 0.19/0.58      ((![X27 : $i, X28 : $i]:
% 0.19/0.58          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.58           | ~ (l1_pre_topc @ X28)
% 0.19/0.58           | ~ (v2_pre_topc @ X28)
% 0.19/0.58           | ((k1_tops_1 @ X28 @ X27) != (X27))
% 0.19/0.58           | (v3_pre_topc @ X27 @ X28)))
% 0.19/0.58         <= ((![X27 : $i, X28 : $i]:
% 0.19/0.58                (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.58                 | ~ (l1_pre_topc @ X28)
% 0.19/0.58                 | ~ (v2_pre_topc @ X28)
% 0.19/0.58                 | ((k1_tops_1 @ X28 @ X27) != (X27))
% 0.19/0.58                 | (v3_pre_topc @ X27 @ X28))))),
% 0.19/0.58      inference('split', [status(esa)], ['42'])).
% 0.19/0.58  thf('44', plain,
% 0.19/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('45', plain,
% 0.19/0.58      ((![X25 : $i, X26 : $i]:
% 0.19/0.58          (~ (l1_pre_topc @ X25)
% 0.19/0.58           | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))))
% 0.19/0.58         <= ((![X25 : $i, X26 : $i]:
% 0.19/0.58                (~ (l1_pre_topc @ X25)
% 0.19/0.58                 | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25))))))),
% 0.19/0.58      inference('split', [status(esa)], ['42'])).
% 0.19/0.58  thf('46', plain,
% 0.19/0.58      ((~ (l1_pre_topc @ sk_A))
% 0.19/0.58         <= ((![X25 : $i, X26 : $i]:
% 0.19/0.58                (~ (l1_pre_topc @ X25)
% 0.19/0.58                 | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25))))))),
% 0.19/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.58  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('48', plain,
% 0.19/0.58      (~
% 0.19/0.58       (![X25 : $i, X26 : $i]:
% 0.19/0.58          (~ (l1_pre_topc @ X25)
% 0.19/0.58           | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))))),
% 0.19/0.58      inference('demod', [status(thm)], ['46', '47'])).
% 0.19/0.58  thf('49', plain,
% 0.19/0.58      ((![X27 : $i, X28 : $i]:
% 0.19/0.58          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.58           | ~ (l1_pre_topc @ X28)
% 0.19/0.58           | ~ (v2_pre_topc @ X28)
% 0.19/0.58           | ((k1_tops_1 @ X28 @ X27) != (X27))
% 0.19/0.58           | (v3_pre_topc @ X27 @ X28))) | 
% 0.19/0.58       (![X25 : $i, X26 : $i]:
% 0.19/0.58          (~ (l1_pre_topc @ X25)
% 0.19/0.58           | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))))),
% 0.19/0.58      inference('split', [status(esa)], ['42'])).
% 0.19/0.58  thf('50', plain,
% 0.19/0.58      ((![X27 : $i, X28 : $i]:
% 0.19/0.58          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.58           | ~ (l1_pre_topc @ X28)
% 0.19/0.58           | ~ (v2_pre_topc @ X28)
% 0.19/0.58           | ((k1_tops_1 @ X28 @ X27) != (X27))
% 0.19/0.58           | (v3_pre_topc @ X27 @ X28)))),
% 0.19/0.58      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.19/0.58  thf('51', plain,
% 0.19/0.58      (![X27 : $i, X28 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.58          | ~ (l1_pre_topc @ X28)
% 0.19/0.58          | ~ (v2_pre_topc @ X28)
% 0.19/0.58          | ((k1_tops_1 @ X28 @ X27) != (X27))
% 0.19/0.58          | (v3_pre_topc @ X27 @ X28))),
% 0.19/0.58      inference('simpl_trail', [status(thm)], ['43', '50'])).
% 0.19/0.58  thf('52', plain,
% 0.19/0.58      (((v3_pre_topc @ sk_B @ sk_A)
% 0.19/0.58        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 0.19/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.58      inference('sup-', [status(thm)], ['41', '51'])).
% 0.19/0.58  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('55', plain,
% 0.19/0.58      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 0.19/0.58      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.19/0.58  thf('56', plain,
% 0.19/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf(t74_tops_1, axiom,
% 0.19/0.58    (![A:$i]:
% 0.19/0.58     ( ( l1_pre_topc @ A ) =>
% 0.19/0.58       ( ![B:$i]:
% 0.19/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.58           ( ( k1_tops_1 @ A @ B ) =
% 0.19/0.58             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.58  thf('57', plain,
% 0.19/0.58      (![X29 : $i, X30 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.19/0.58          | ((k1_tops_1 @ X30 @ X29)
% 0.19/0.58              = (k7_subset_1 @ (u1_struct_0 @ X30) @ X29 @ 
% 0.19/0.58                 (k2_tops_1 @ X30 @ X29)))
% 0.19/0.58          | ~ (l1_pre_topc @ X30))),
% 0.19/0.58      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.19/0.58  thf('58', plain,
% 0.19/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.58        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.19/0.58            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.58               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.19/0.58  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('60', plain,
% 0.19/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('61', plain,
% 0.19/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.19/0.58          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.19/0.58      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.19/0.58  thf('62', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.19/0.58           = (k4_xboole_0 @ sk_B @ X0))),
% 0.19/0.58      inference('sup-', [status(thm)], ['60', '61'])).
% 0.19/0.58  thf('63', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.19/0.58           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.19/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.58  thf('64', plain,
% 0.19/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.19/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.19/0.58      inference('split', [status(esa)], ['3'])).
% 0.19/0.58  thf('65', plain,
% 0.19/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.19/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.19/0.58      inference('sup+', [status(thm)], ['63', '64'])).
% 0.19/0.58  thf(d4_xboole_0, axiom,
% 0.19/0.58    (![A:$i,B:$i,C:$i]:
% 0.19/0.58     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.19/0.58       ( ![D:$i]:
% 0.19/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.58           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.19/0.58  thf('66', plain,
% 0.19/0.58      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.19/0.58         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.19/0.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.19/0.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.19/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.19/0.58  thf(t3_boole, axiom,
% 0.19/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.58  thf('67', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.19/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.58  thf(d5_xboole_0, axiom,
% 0.19/0.58    (![A:$i,B:$i,C:$i]:
% 0.19/0.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.58       ( ![D:$i]:
% 0.19/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.58  thf('68', plain,
% 0.19/0.58      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.58         (~ (r2_hidden @ X10 @ X9)
% 0.19/0.58          | ~ (r2_hidden @ X10 @ X8)
% 0.19/0.58          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.19/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.58  thf('69', plain,
% 0.19/0.58      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.19/0.58         (~ (r2_hidden @ X10 @ X8)
% 0.19/0.58          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.19/0.58      inference('simplify', [status(thm)], ['68'])).
% 0.19/0.58  thf('70', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.19/0.58      inference('sup-', [status(thm)], ['67', '69'])).
% 0.19/0.58  thf('71', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.58      inference('condensation', [status(thm)], ['70'])).
% 0.19/0.58  thf('72', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.19/0.58          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['66', '71'])).
% 0.19/0.58  thf(t2_boole, axiom,
% 0.19/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.58  thf('73', plain,
% 0.19/0.58      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.58  thf('74', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.19/0.58          | ((X1) = (k1_xboole_0)))),
% 0.19/0.58      inference('demod', [status(thm)], ['72', '73'])).
% 0.19/0.58  thf('75', plain,
% 0.19/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.58          | (r2_hidden @ X4 @ X1)
% 0.19/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.19/0.58  thf('76', plain,
% 0.19/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.58         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.58      inference('simplify', [status(thm)], ['75'])).
% 0.19/0.58  thf('77', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.19/0.58          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0 @ X2) @ 
% 0.19/0.58             X1))),
% 0.19/0.58      inference('sup-', [status(thm)], ['74', '76'])).
% 0.19/0.58  thf('78', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.19/0.58          | ((X1) = (k1_xboole_0)))),
% 0.19/0.58      inference('demod', [status(thm)], ['72', '73'])).
% 0.19/0.58  thf('79', plain,
% 0.19/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.58          | (r2_hidden @ X4 @ X2)
% 0.19/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.19/0.58  thf('80', plain,
% 0.19/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.58         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.58      inference('simplify', [status(thm)], ['79'])).
% 0.19/0.58  thf('81', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.19/0.58          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0 @ X2) @ 
% 0.19/0.58             X0))),
% 0.19/0.58      inference('sup-', [status(thm)], ['78', '80'])).
% 0.19/0.58  thf('82', plain,
% 0.19/0.58      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.19/0.58         (~ (r2_hidden @ X10 @ X8)
% 0.19/0.58          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.19/0.58      inference('simplify', [status(thm)], ['68'])).
% 0.19/0.58  thf('83', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.58         (((k3_xboole_0 @ X3 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))
% 0.19/0.58          | ~ (r2_hidden @ 
% 0.19/0.58               (sk_D @ (k3_xboole_0 @ X3 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.19/0.58                k1_xboole_0 @ X2) @ 
% 0.19/0.58               X0))),
% 0.19/0.58      inference('sup-', [status(thm)], ['81', '82'])).
% 0.19/0.58  thf('84', plain,
% 0.19/0.58      (![X0 : $i, X2 : $i]:
% 0.19/0.58         (((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X0)) = (k1_xboole_0))
% 0.19/0.58          | ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X0)) = (k1_xboole_0)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['77', '83'])).
% 0.19/0.58  thf('85', plain,
% 0.19/0.58      (![X0 : $i, X2 : $i]:
% 0.19/0.58         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X0)) = (k1_xboole_0))),
% 0.19/0.58      inference('simplify', [status(thm)], ['84'])).
% 0.19/0.58  thf('86', plain,
% 0.19/0.58      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 0.19/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.19/0.58      inference('sup+', [status(thm)], ['65', '85'])).
% 0.19/0.58  thf(t100_xboole_1, axiom,
% 0.19/0.58    (![A:$i,B:$i]:
% 0.19/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.58  thf('87', plain,
% 0.19/0.58      (![X12 : $i, X13 : $i]:
% 0.19/0.58         ((k4_xboole_0 @ X12 @ X13)
% 0.19/0.58           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.19/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.58  thf('88', plain,
% 0.19/0.58      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.19/0.58          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.19/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.19/0.58      inference('sup+', [status(thm)], ['86', '87'])).
% 0.19/0.58  thf('89', plain,
% 0.19/0.58      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.58  thf('90', plain,
% 0.19/0.58      (![X12 : $i, X13 : $i]:
% 0.19/0.58         ((k4_xboole_0 @ X12 @ X13)
% 0.19/0.58           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.19/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.58  thf('91', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.58      inference('sup+', [status(thm)], ['89', '90'])).
% 0.19/0.58  thf('92', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.19/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.58  thf('93', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.19/0.58      inference('sup+', [status(thm)], ['91', '92'])).
% 0.19/0.58  thf('94', plain,
% 0.19/0.58      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.19/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.19/0.58      inference('demod', [status(thm)], ['88', '93'])).
% 0.19/0.58  thf('95', plain,
% 0.19/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.19/0.58       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.19/0.58      inference('split', [status(esa)], ['3'])).
% 0.19/0.58  thf('96', plain,
% 0.19/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.19/0.58      inference('sat_resolution*', [status(thm)], ['2', '38', '95'])).
% 0.19/0.58  thf('97', plain,
% 0.19/0.58      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.19/0.58      inference('simpl_trail', [status(thm)], ['94', '96'])).
% 0.19/0.58  thf('98', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['58', '59', '62', '97'])).
% 0.19/0.58  thf('99', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.19/0.58      inference('demod', [status(thm)], ['55', '98'])).
% 0.19/0.58  thf('100', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.19/0.58      inference('simplify', [status(thm)], ['99'])).
% 0.19/0.58  thf('101', plain, ($false), inference('demod', [status(thm)], ['40', '100'])).
% 0.19/0.58  
% 0.19/0.58  % SZS output end Refutation
% 0.19/0.58  
% 0.19/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
