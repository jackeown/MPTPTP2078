%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NNXZYpqybN

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:31 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 403 expanded)
%              Number of leaves         :   32 ( 123 expanded)
%              Depth                    :   24
%              Number of atoms          : 1508 (5206 expanded)
%              Number of equality atoms :  111 ( 314 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k2_tops_1 @ X26 @ X25 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k2_pre_topc @ X26 @ X25 ) @ ( k1_tops_1 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
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

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('56',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('57',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('58',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('59',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['60'])).

thf('66',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','66'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('70',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('71',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','66'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('80',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('84',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','38','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X1 ) @ X0 @ k1_xboole_0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','85'])).

thf('87',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('90',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['90'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('92',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('95',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('97',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('98',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['97'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('99',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('102',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['96','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('109',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['96','104'])).

thf('113',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('116',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['111','116'])).

thf('118',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['93','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('120',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k1_tops_1 @ X32 @ X31 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 @ ( k2_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('121',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['121','122','125'])).

thf('127',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['118','126'])).

thf('128',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['55','127'])).

thf('129',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    $false ),
    inference(demod,[status(thm)],['40','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NNXZYpqybN
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.09/1.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.09/1.29  % Solved by: fo/fo7.sh
% 1.09/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.09/1.29  % done 1012 iterations in 0.832s
% 1.09/1.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.09/1.29  % SZS output start Refutation
% 1.09/1.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.09/1.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.09/1.29  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.09/1.29  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.09/1.29  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.09/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.09/1.29  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.09/1.29  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.09/1.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.09/1.29  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.09/1.29  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.09/1.29  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.09/1.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.09/1.29  thf(sk_B_type, type, sk_B: $i).
% 1.09/1.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.09/1.29  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.09/1.29  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.09/1.29  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.09/1.29  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.09/1.29  thf(t76_tops_1, conjecture,
% 1.09/1.29    (![A:$i]:
% 1.09/1.29     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.09/1.29       ( ![B:$i]:
% 1.09/1.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.09/1.29           ( ( v3_pre_topc @ B @ A ) <=>
% 1.09/1.29             ( ( k2_tops_1 @ A @ B ) =
% 1.09/1.29               ( k7_subset_1 @
% 1.09/1.29                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 1.09/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.09/1.29    (~( ![A:$i]:
% 1.09/1.29        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.09/1.29          ( ![B:$i]:
% 1.09/1.29            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.09/1.29              ( ( v3_pre_topc @ B @ A ) <=>
% 1.09/1.29                ( ( k2_tops_1 @ A @ B ) =
% 1.09/1.29                  ( k7_subset_1 @
% 1.09/1.29                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 1.09/1.29    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 1.09/1.29  thf('0', plain,
% 1.09/1.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.09/1.29        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('1', plain,
% 1.09/1.29      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.09/1.29      inference('split', [status(esa)], ['0'])).
% 1.09/1.29  thf('2', plain,
% 1.09/1.29      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 1.09/1.29       ~
% 1.09/1.29       (((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 1.09/1.29      inference('split', [status(esa)], ['0'])).
% 1.09/1.29  thf('3', plain,
% 1.09/1.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.09/1.29        | (v3_pre_topc @ sk_B @ sk_A))),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('4', plain,
% 1.09/1.29      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.09/1.29      inference('split', [status(esa)], ['3'])).
% 1.09/1.29  thf('5', plain,
% 1.09/1.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf(t55_tops_1, axiom,
% 1.09/1.29    (![A:$i]:
% 1.09/1.29     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.09/1.29       ( ![B:$i]:
% 1.09/1.29         ( ( l1_pre_topc @ B ) =>
% 1.09/1.29           ( ![C:$i]:
% 1.09/1.29             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.09/1.29               ( ![D:$i]:
% 1.09/1.29                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.09/1.29                   ( ( ( v3_pre_topc @ D @ B ) =>
% 1.09/1.29                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 1.09/1.29                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 1.09/1.29                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 1.09/1.29  thf('6', plain,
% 1.09/1.29      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.09/1.29         (~ (l1_pre_topc @ X27)
% 1.09/1.29          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.09/1.29          | ~ (v3_pre_topc @ X28 @ X27)
% 1.09/1.29          | ((k1_tops_1 @ X27 @ X28) = (X28))
% 1.09/1.29          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.09/1.29          | ~ (l1_pre_topc @ X30)
% 1.09/1.29          | ~ (v2_pre_topc @ X30))),
% 1.09/1.29      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.09/1.29  thf('7', plain,
% 1.09/1.29      ((![X27 : $i, X28 : $i]:
% 1.09/1.29          (~ (l1_pre_topc @ X27)
% 1.09/1.29           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.09/1.29           | ~ (v3_pre_topc @ X28 @ X27)
% 1.09/1.29           | ((k1_tops_1 @ X27 @ X28) = (X28))))
% 1.09/1.29         <= ((![X27 : $i, X28 : $i]:
% 1.09/1.29                (~ (l1_pre_topc @ X27)
% 1.09/1.29                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.09/1.29                 | ~ (v3_pre_topc @ X28 @ X27)
% 1.09/1.29                 | ((k1_tops_1 @ X27 @ X28) = (X28)))))),
% 1.09/1.29      inference('split', [status(esa)], ['6'])).
% 1.09/1.29  thf('8', plain,
% 1.09/1.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('9', plain,
% 1.09/1.29      ((![X29 : $i, X30 : $i]:
% 1.09/1.29          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.09/1.29           | ~ (l1_pre_topc @ X30)
% 1.09/1.29           | ~ (v2_pre_topc @ X30)))
% 1.09/1.29         <= ((![X29 : $i, X30 : $i]:
% 1.09/1.29                (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.09/1.29                 | ~ (l1_pre_topc @ X30)
% 1.09/1.29                 | ~ (v2_pre_topc @ X30))))),
% 1.09/1.29      inference('split', [status(esa)], ['6'])).
% 1.09/1.29  thf('10', plain,
% 1.09/1.29      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 1.09/1.29         <= ((![X29 : $i, X30 : $i]:
% 1.09/1.29                (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.09/1.29                 | ~ (l1_pre_topc @ X30)
% 1.09/1.29                 | ~ (v2_pre_topc @ X30))))),
% 1.09/1.29      inference('sup-', [status(thm)], ['8', '9'])).
% 1.09/1.29  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('13', plain,
% 1.09/1.29      (~
% 1.09/1.29       (![X29 : $i, X30 : $i]:
% 1.09/1.29          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.09/1.29           | ~ (l1_pre_topc @ X30)
% 1.09/1.29           | ~ (v2_pre_topc @ X30)))),
% 1.09/1.29      inference('demod', [status(thm)], ['10', '11', '12'])).
% 1.09/1.29  thf('14', plain,
% 1.09/1.29      ((![X27 : $i, X28 : $i]:
% 1.09/1.29          (~ (l1_pre_topc @ X27)
% 1.09/1.29           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.09/1.29           | ~ (v3_pre_topc @ X28 @ X27)
% 1.09/1.29           | ((k1_tops_1 @ X27 @ X28) = (X28)))) | 
% 1.09/1.29       (![X29 : $i, X30 : $i]:
% 1.09/1.29          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.09/1.29           | ~ (l1_pre_topc @ X30)
% 1.09/1.29           | ~ (v2_pre_topc @ X30)))),
% 1.09/1.29      inference('split', [status(esa)], ['6'])).
% 1.09/1.29  thf('15', plain,
% 1.09/1.29      ((![X27 : $i, X28 : $i]:
% 1.09/1.29          (~ (l1_pre_topc @ X27)
% 1.09/1.29           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.09/1.29           | ~ (v3_pre_topc @ X28 @ X27)
% 1.09/1.29           | ((k1_tops_1 @ X27 @ X28) = (X28))))),
% 1.09/1.29      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 1.09/1.29  thf('16', plain,
% 1.09/1.29      (![X27 : $i, X28 : $i]:
% 1.09/1.29         (~ (l1_pre_topc @ X27)
% 1.09/1.29          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.09/1.29          | ~ (v3_pre_topc @ X28 @ X27)
% 1.09/1.29          | ((k1_tops_1 @ X27 @ X28) = (X28)))),
% 1.09/1.29      inference('simpl_trail', [status(thm)], ['7', '15'])).
% 1.09/1.29  thf('17', plain,
% 1.09/1.29      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 1.09/1.29        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 1.09/1.29        | ~ (l1_pre_topc @ sk_A))),
% 1.09/1.29      inference('sup-', [status(thm)], ['5', '16'])).
% 1.09/1.29  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('19', plain,
% 1.09/1.29      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.09/1.29      inference('demod', [status(thm)], ['17', '18'])).
% 1.09/1.29  thf('20', plain,
% 1.09/1.29      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.09/1.29         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.09/1.29      inference('sup-', [status(thm)], ['4', '19'])).
% 1.09/1.29  thf('21', plain,
% 1.09/1.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf(l78_tops_1, axiom,
% 1.09/1.29    (![A:$i]:
% 1.09/1.29     ( ( l1_pre_topc @ A ) =>
% 1.09/1.29       ( ![B:$i]:
% 1.09/1.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.09/1.29           ( ( k2_tops_1 @ A @ B ) =
% 1.09/1.29             ( k7_subset_1 @
% 1.09/1.29               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.09/1.29               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.09/1.29  thf('22', plain,
% 1.09/1.29      (![X25 : $i, X26 : $i]:
% 1.09/1.29         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.09/1.29          | ((k2_tops_1 @ X26 @ X25)
% 1.09/1.29              = (k7_subset_1 @ (u1_struct_0 @ X26) @ 
% 1.09/1.29                 (k2_pre_topc @ X26 @ X25) @ (k1_tops_1 @ X26 @ X25)))
% 1.09/1.29          | ~ (l1_pre_topc @ X26))),
% 1.09/1.29      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.09/1.29  thf('23', plain,
% 1.09/1.29      ((~ (l1_pre_topc @ sk_A)
% 1.09/1.29        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.09/1.29      inference('sup-', [status(thm)], ['21', '22'])).
% 1.09/1.29  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('25', plain,
% 1.09/1.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf(dt_k2_pre_topc, axiom,
% 1.09/1.29    (![A:$i,B:$i]:
% 1.09/1.29     ( ( ( l1_pre_topc @ A ) & 
% 1.09/1.29         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.09/1.29       ( m1_subset_1 @
% 1.09/1.29         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.09/1.29  thf('26', plain,
% 1.09/1.29      (![X23 : $i, X24 : $i]:
% 1.09/1.29         (~ (l1_pre_topc @ X23)
% 1.09/1.29          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.09/1.29          | (m1_subset_1 @ (k2_pre_topc @ X23 @ X24) @ 
% 1.09/1.29             (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 1.09/1.29      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.09/1.29  thf('27', plain,
% 1.09/1.29      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.09/1.29         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.09/1.29        | ~ (l1_pre_topc @ sk_A))),
% 1.09/1.29      inference('sup-', [status(thm)], ['25', '26'])).
% 1.09/1.29  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('29', plain,
% 1.09/1.29      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.09/1.29        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.09/1.29      inference('demod', [status(thm)], ['27', '28'])).
% 1.09/1.29  thf(redefinition_k7_subset_1, axiom,
% 1.09/1.29    (![A:$i,B:$i,C:$i]:
% 1.09/1.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.09/1.29       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.09/1.29  thf('30', plain,
% 1.09/1.29      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.09/1.29         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 1.09/1.29          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 1.09/1.29      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.09/1.29  thf('31', plain,
% 1.09/1.29      (![X0 : $i]:
% 1.09/1.29         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.09/1.29           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['29', '30'])).
% 1.09/1.29  thf('32', plain,
% 1.09/1.29      (((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.09/1.29            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.09/1.29      inference('demod', [status(thm)], ['23', '24', '31'])).
% 1.09/1.29  thf('33', plain,
% 1.09/1.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.09/1.29         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.09/1.29      inference('sup+', [status(thm)], ['20', '32'])).
% 1.09/1.29  thf('34', plain,
% 1.09/1.29      (![X0 : $i]:
% 1.09/1.29         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.09/1.29           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['29', '30'])).
% 1.09/1.29  thf('35', plain,
% 1.09/1.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.09/1.29         <= (~
% 1.09/1.29             (((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.09/1.29      inference('split', [status(esa)], ['0'])).
% 1.09/1.29  thf('36', plain,
% 1.09/1.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.09/1.29         <= (~
% 1.09/1.29             (((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.09/1.29      inference('sup-', [status(thm)], ['34', '35'])).
% 1.09/1.29  thf('37', plain,
% 1.09/1.29      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.09/1.29         <= (~
% 1.09/1.29             (((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 1.09/1.29             ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.09/1.29      inference('sup-', [status(thm)], ['33', '36'])).
% 1.09/1.29  thf('38', plain,
% 1.09/1.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.09/1.29       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.09/1.29      inference('simplify', [status(thm)], ['37'])).
% 1.09/1.29  thf('39', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.09/1.29      inference('sat_resolution*', [status(thm)], ['2', '38'])).
% 1.09/1.29  thf('40', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 1.09/1.29      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 1.09/1.29  thf('41', plain,
% 1.09/1.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('42', plain,
% 1.09/1.29      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.09/1.29         (~ (l1_pre_topc @ X27)
% 1.09/1.29          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.09/1.29          | ((k1_tops_1 @ X30 @ X29) != (X29))
% 1.09/1.29          | (v3_pre_topc @ X29 @ X30)
% 1.09/1.29          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.09/1.29          | ~ (l1_pre_topc @ X30)
% 1.09/1.29          | ~ (v2_pre_topc @ X30))),
% 1.09/1.29      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.09/1.29  thf('43', plain,
% 1.09/1.29      ((![X29 : $i, X30 : $i]:
% 1.09/1.29          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.09/1.29           | ~ (l1_pre_topc @ X30)
% 1.09/1.29           | ~ (v2_pre_topc @ X30)
% 1.09/1.29           | ((k1_tops_1 @ X30 @ X29) != (X29))
% 1.09/1.29           | (v3_pre_topc @ X29 @ X30)))
% 1.09/1.29         <= ((![X29 : $i, X30 : $i]:
% 1.09/1.29                (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.09/1.29                 | ~ (l1_pre_topc @ X30)
% 1.09/1.29                 | ~ (v2_pre_topc @ X30)
% 1.09/1.29                 | ((k1_tops_1 @ X30 @ X29) != (X29))
% 1.09/1.29                 | (v3_pre_topc @ X29 @ X30))))),
% 1.09/1.29      inference('split', [status(esa)], ['42'])).
% 1.09/1.29  thf('44', plain,
% 1.09/1.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('45', plain,
% 1.09/1.29      ((![X27 : $i, X28 : $i]:
% 1.09/1.29          (~ (l1_pre_topc @ X27)
% 1.09/1.29           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))))
% 1.09/1.29         <= ((![X27 : $i, X28 : $i]:
% 1.09/1.29                (~ (l1_pre_topc @ X27)
% 1.09/1.29                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))))),
% 1.09/1.29      inference('split', [status(esa)], ['42'])).
% 1.09/1.29  thf('46', plain,
% 1.09/1.29      ((~ (l1_pre_topc @ sk_A))
% 1.09/1.29         <= ((![X27 : $i, X28 : $i]:
% 1.09/1.29                (~ (l1_pre_topc @ X27)
% 1.09/1.29                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))))),
% 1.09/1.29      inference('sup-', [status(thm)], ['44', '45'])).
% 1.09/1.29  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('48', plain,
% 1.09/1.29      (~
% 1.09/1.29       (![X27 : $i, X28 : $i]:
% 1.09/1.29          (~ (l1_pre_topc @ X27)
% 1.09/1.29           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))))),
% 1.09/1.29      inference('demod', [status(thm)], ['46', '47'])).
% 1.09/1.29  thf('49', plain,
% 1.09/1.29      ((![X29 : $i, X30 : $i]:
% 1.09/1.29          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.09/1.29           | ~ (l1_pre_topc @ X30)
% 1.09/1.29           | ~ (v2_pre_topc @ X30)
% 1.09/1.29           | ((k1_tops_1 @ X30 @ X29) != (X29))
% 1.09/1.29           | (v3_pre_topc @ X29 @ X30))) | 
% 1.09/1.29       (![X27 : $i, X28 : $i]:
% 1.09/1.29          (~ (l1_pre_topc @ X27)
% 1.09/1.29           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))))),
% 1.09/1.29      inference('split', [status(esa)], ['42'])).
% 1.09/1.29  thf('50', plain,
% 1.09/1.29      ((![X29 : $i, X30 : $i]:
% 1.09/1.29          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.09/1.29           | ~ (l1_pre_topc @ X30)
% 1.09/1.29           | ~ (v2_pre_topc @ X30)
% 1.09/1.29           | ((k1_tops_1 @ X30 @ X29) != (X29))
% 1.09/1.29           | (v3_pre_topc @ X29 @ X30)))),
% 1.09/1.29      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 1.09/1.29  thf('51', plain,
% 1.09/1.29      (![X29 : $i, X30 : $i]:
% 1.09/1.29         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.09/1.29          | ~ (l1_pre_topc @ X30)
% 1.09/1.29          | ~ (v2_pre_topc @ X30)
% 1.09/1.29          | ((k1_tops_1 @ X30 @ X29) != (X29))
% 1.09/1.29          | (v3_pre_topc @ X29 @ X30))),
% 1.09/1.29      inference('simpl_trail', [status(thm)], ['43', '50'])).
% 1.09/1.29  thf('52', plain,
% 1.09/1.29      (((v3_pre_topc @ sk_B @ sk_A)
% 1.09/1.29        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 1.09/1.29        | ~ (v2_pre_topc @ sk_A)
% 1.09/1.29        | ~ (l1_pre_topc @ sk_A))),
% 1.09/1.29      inference('sup-', [status(thm)], ['41', '51'])).
% 1.09/1.29  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('55', plain,
% 1.09/1.29      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 1.09/1.29      inference('demod', [status(thm)], ['52', '53', '54'])).
% 1.09/1.29  thf(d5_xboole_0, axiom,
% 1.09/1.29    (![A:$i,B:$i,C:$i]:
% 1.09/1.29     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.09/1.29       ( ![D:$i]:
% 1.09/1.29         ( ( r2_hidden @ D @ C ) <=>
% 1.09/1.29           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.09/1.29  thf('56', plain,
% 1.09/1.29      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.09/1.29         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.09/1.29          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.09/1.29          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.09/1.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.09/1.29  thf(t3_boole, axiom,
% 1.09/1.29    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.09/1.29  thf('57', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.09/1.29      inference('cnf', [status(esa)], [t3_boole])).
% 1.09/1.29  thf('58', plain,
% 1.09/1.29      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.09/1.29         (~ (r2_hidden @ X6 @ X5)
% 1.09/1.29          | ~ (r2_hidden @ X6 @ X4)
% 1.09/1.29          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.09/1.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.09/1.29  thf('59', plain,
% 1.09/1.29      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.09/1.29         (~ (r2_hidden @ X6 @ X4)
% 1.09/1.29          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.09/1.29      inference('simplify', [status(thm)], ['58'])).
% 1.09/1.29  thf('60', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]:
% 1.09/1.29         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['57', '59'])).
% 1.09/1.29  thf('61', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.09/1.29      inference('condensation', [status(thm)], ['60'])).
% 1.09/1.29  thf('62', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]:
% 1.09/1.29         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.09/1.29          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.09/1.29      inference('sup-', [status(thm)], ['56', '61'])).
% 1.09/1.29  thf('63', plain,
% 1.09/1.29      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.09/1.29         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.09/1.29          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.09/1.29          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.09/1.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.09/1.29  thf('64', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]:
% 1.09/1.29         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.09/1.29          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.09/1.29      inference('eq_fact', [status(thm)], ['63'])).
% 1.09/1.29  thf('65', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.09/1.29      inference('condensation', [status(thm)], ['60'])).
% 1.09/1.29  thf('66', plain,
% 1.09/1.29      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['64', '65'])).
% 1.09/1.29  thf('67', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]:
% 1.09/1.29         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.09/1.29          | ((X1) = (k1_xboole_0)))),
% 1.09/1.29      inference('demod', [status(thm)], ['62', '66'])).
% 1.09/1.29  thf(commutativity_k3_xboole_0, axiom,
% 1.09/1.29    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.09/1.29  thf('68', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.09/1.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.09/1.29  thf(t48_xboole_1, axiom,
% 1.09/1.29    (![A:$i,B:$i]:
% 1.09/1.29     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.09/1.29  thf('69', plain,
% 1.09/1.29      (![X16 : $i, X17 : $i]:
% 1.09/1.29         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.09/1.29           = (k3_xboole_0 @ X16 @ X17))),
% 1.09/1.29      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.09/1.29  thf('70', plain,
% 1.09/1.29      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.09/1.29         (~ (r2_hidden @ X6 @ X5)
% 1.09/1.29          | (r2_hidden @ X6 @ X3)
% 1.09/1.29          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.09/1.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.09/1.29  thf('71', plain,
% 1.09/1.29      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.09/1.29         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.09/1.29      inference('simplify', [status(thm)], ['70'])).
% 1.09/1.29  thf('72', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.29         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 1.09/1.29      inference('sup-', [status(thm)], ['69', '71'])).
% 1.09/1.29  thf('73', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.29         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['68', '72'])).
% 1.09/1.29  thf('74', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.29         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.09/1.29          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 1.09/1.29             X0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['67', '73'])).
% 1.09/1.29  thf('75', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]:
% 1.09/1.29         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.09/1.29          | ((X1) = (k1_xboole_0)))),
% 1.09/1.29      inference('demod', [status(thm)], ['62', '66'])).
% 1.09/1.29  thf('76', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.29         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 1.09/1.29      inference('sup-', [status(thm)], ['69', '71'])).
% 1.09/1.29  thf('77', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.29         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.09/1.29          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 1.09/1.29             X1))),
% 1.09/1.29      inference('sup-', [status(thm)], ['75', '76'])).
% 1.09/1.29  thf('78', plain,
% 1.09/1.29      (![X0 : $i]:
% 1.09/1.29         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.09/1.29           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['29', '30'])).
% 1.09/1.29  thf('79', plain,
% 1.09/1.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.09/1.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.09/1.29      inference('split', [status(esa)], ['3'])).
% 1.09/1.29  thf('80', plain,
% 1.09/1.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.09/1.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.09/1.29      inference('sup+', [status(thm)], ['78', '79'])).
% 1.09/1.29  thf('81', plain,
% 1.09/1.29      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.09/1.29         (~ (r2_hidden @ X6 @ X4)
% 1.09/1.29          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.09/1.29      inference('simplify', [status(thm)], ['58'])).
% 1.09/1.29  thf('82', plain,
% 1.09/1.29      ((![X0 : $i]:
% 1.09/1.29          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 1.09/1.29           | ~ (r2_hidden @ X0 @ sk_B)))
% 1.09/1.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.09/1.29      inference('sup-', [status(thm)], ['80', '81'])).
% 1.09/1.29  thf('83', plain,
% 1.09/1.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.09/1.29       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.09/1.29      inference('split', [status(esa)], ['3'])).
% 1.09/1.29  thf('84', plain,
% 1.09/1.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.09/1.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.09/1.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 1.09/1.29      inference('sat_resolution*', [status(thm)], ['2', '38', '83'])).
% 1.09/1.29  thf('85', plain,
% 1.09/1.29      (![X0 : $i]:
% 1.09/1.29         (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 1.09/1.29          | ~ (r2_hidden @ X0 @ sk_B))),
% 1.09/1.29      inference('simpl_trail', [status(thm)], ['82', '84'])).
% 1.09/1.29  thf('86', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]:
% 1.09/1.29         (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X1) = (k1_xboole_0))
% 1.09/1.29          | ~ (r2_hidden @ 
% 1.09/1.29               (sk_D @ (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X1) @ X0 @ 
% 1.09/1.29                k1_xboole_0) @ 
% 1.09/1.29               sk_B))),
% 1.09/1.29      inference('sup-', [status(thm)], ['77', '85'])).
% 1.09/1.29  thf('87', plain,
% 1.09/1.29      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))
% 1.09/1.29        | ((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))),
% 1.09/1.29      inference('sup-', [status(thm)], ['74', '86'])).
% 1.09/1.29  thf('88', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.09/1.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.09/1.29  thf('89', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.09/1.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.09/1.29  thf('90', plain,
% 1.09/1.29      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 1.09/1.29        | ((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 1.09/1.29      inference('demod', [status(thm)], ['87', '88', '89'])).
% 1.09/1.29  thf('91', plain,
% 1.09/1.29      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 1.09/1.29      inference('simplify', [status(thm)], ['90'])).
% 1.09/1.29  thf(t100_xboole_1, axiom,
% 1.09/1.29    (![A:$i,B:$i]:
% 1.09/1.29     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.09/1.29  thf('92', plain,
% 1.09/1.29      (![X11 : $i, X12 : $i]:
% 1.09/1.29         ((k4_xboole_0 @ X11 @ X12)
% 1.09/1.29           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.09/1.29      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.09/1.29  thf('93', plain,
% 1.09/1.29      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.09/1.29         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 1.09/1.29      inference('sup+', [status(thm)], ['91', '92'])).
% 1.09/1.29  thf('94', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.09/1.29      inference('cnf', [status(esa)], [t3_boole])).
% 1.09/1.29  thf('95', plain,
% 1.09/1.29      (![X16 : $i, X17 : $i]:
% 1.09/1.29         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.09/1.29           = (k3_xboole_0 @ X16 @ X17))),
% 1.09/1.29      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.09/1.29  thf('96', plain,
% 1.09/1.29      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.09/1.29      inference('sup+', [status(thm)], ['94', '95'])).
% 1.09/1.29  thf(d10_xboole_0, axiom,
% 1.09/1.29    (![A:$i,B:$i]:
% 1.09/1.29     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.09/1.29  thf('97', plain,
% 1.09/1.29      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 1.09/1.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.09/1.29  thf('98', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.09/1.29      inference('simplify', [status(thm)], ['97'])).
% 1.09/1.29  thf(t28_xboole_1, axiom,
% 1.09/1.29    (![A:$i,B:$i]:
% 1.09/1.29     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.09/1.29  thf('99', plain,
% 1.09/1.29      (![X13 : $i, X14 : $i]:
% 1.09/1.29         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.09/1.29      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.09/1.29  thf('100', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['98', '99'])).
% 1.09/1.29  thf('101', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.09/1.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.09/1.29  thf('102', plain,
% 1.09/1.29      (![X11 : $i, X12 : $i]:
% 1.09/1.29         ((k4_xboole_0 @ X11 @ X12)
% 1.09/1.29           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.09/1.29      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.09/1.29  thf('103', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]:
% 1.09/1.29         ((k4_xboole_0 @ X0 @ X1)
% 1.09/1.29           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.09/1.29      inference('sup+', [status(thm)], ['101', '102'])).
% 1.09/1.29  thf('104', plain,
% 1.09/1.29      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.09/1.29      inference('sup+', [status(thm)], ['100', '103'])).
% 1.09/1.29  thf('105', plain,
% 1.09/1.29      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.09/1.29      inference('demod', [status(thm)], ['96', '104'])).
% 1.09/1.29  thf('106', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.09/1.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.09/1.29  thf('107', plain,
% 1.09/1.29      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.09/1.29      inference('sup+', [status(thm)], ['105', '106'])).
% 1.09/1.29  thf('108', plain,
% 1.09/1.29      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['64', '65'])).
% 1.09/1.29  thf('109', plain,
% 1.09/1.29      (![X16 : $i, X17 : $i]:
% 1.09/1.29         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.09/1.29           = (k3_xboole_0 @ X16 @ X17))),
% 1.09/1.29      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.09/1.29  thf('110', plain,
% 1.09/1.29      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.09/1.29      inference('sup+', [status(thm)], ['108', '109'])).
% 1.09/1.29  thf('111', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.09/1.29      inference('demod', [status(thm)], ['107', '110'])).
% 1.09/1.29  thf('112', plain,
% 1.09/1.29      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.09/1.29      inference('demod', [status(thm)], ['96', '104'])).
% 1.09/1.29  thf('113', plain,
% 1.09/1.29      (![X11 : $i, X12 : $i]:
% 1.09/1.29         ((k4_xboole_0 @ X11 @ X12)
% 1.09/1.29           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.09/1.29      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.09/1.29  thf('114', plain,
% 1.09/1.29      (![X0 : $i]:
% 1.09/1.29         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 1.09/1.29           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.09/1.29      inference('sup+', [status(thm)], ['112', '113'])).
% 1.09/1.29  thf('115', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.09/1.29      inference('cnf', [status(esa)], [t3_boole])).
% 1.09/1.29  thf('116', plain,
% 1.09/1.29      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.09/1.29      inference('demod', [status(thm)], ['114', '115'])).
% 1.09/1.29  thf('117', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.09/1.29      inference('sup+', [status(thm)], ['111', '116'])).
% 1.09/1.29  thf('118', plain,
% 1.09/1.29      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 1.09/1.29      inference('demod', [status(thm)], ['93', '117'])).
% 1.09/1.29  thf('119', plain,
% 1.09/1.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf(t74_tops_1, axiom,
% 1.09/1.29    (![A:$i]:
% 1.09/1.29     ( ( l1_pre_topc @ A ) =>
% 1.09/1.29       ( ![B:$i]:
% 1.09/1.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.09/1.29           ( ( k1_tops_1 @ A @ B ) =
% 1.09/1.29             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.09/1.29  thf('120', plain,
% 1.09/1.29      (![X31 : $i, X32 : $i]:
% 1.09/1.29         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.09/1.29          | ((k1_tops_1 @ X32 @ X31)
% 1.09/1.29              = (k7_subset_1 @ (u1_struct_0 @ X32) @ X31 @ 
% 1.09/1.29                 (k2_tops_1 @ X32 @ X31)))
% 1.09/1.29          | ~ (l1_pre_topc @ X32))),
% 1.09/1.29      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.09/1.29  thf('121', plain,
% 1.09/1.29      ((~ (l1_pre_topc @ sk_A)
% 1.09/1.29        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.09/1.29            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.09/1.29               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.09/1.29      inference('sup-', [status(thm)], ['119', '120'])).
% 1.09/1.29  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('123', plain,
% 1.09/1.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf('124', plain,
% 1.09/1.29      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.09/1.29         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 1.09/1.29          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 1.09/1.29      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.09/1.29  thf('125', plain,
% 1.09/1.29      (![X0 : $i]:
% 1.09/1.29         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.09/1.29           = (k4_xboole_0 @ sk_B @ X0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['123', '124'])).
% 1.09/1.29  thf('126', plain,
% 1.09/1.29      (((k1_tops_1 @ sk_A @ sk_B)
% 1.09/1.29         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.09/1.29      inference('demod', [status(thm)], ['121', '122', '125'])).
% 1.09/1.29  thf('127', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 1.09/1.29      inference('sup+', [status(thm)], ['118', '126'])).
% 1.09/1.29  thf('128', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 1.09/1.29      inference('demod', [status(thm)], ['55', '127'])).
% 1.09/1.29  thf('129', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 1.09/1.29      inference('simplify', [status(thm)], ['128'])).
% 1.09/1.29  thf('130', plain, ($false), inference('demod', [status(thm)], ['40', '129'])).
% 1.09/1.29  
% 1.09/1.29  % SZS output end Refutation
% 1.09/1.29  
% 1.09/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
