%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mLgOAatj80

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:31 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  192 (1906 expanded)
%              Number of leaves         :   32 ( 602 expanded)
%              Depth                    :   24
%              Number of atoms          : 1800 (17239 expanded)
%              Number of equality atoms :  136 (1652 expanded)
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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('58',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('66',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['67'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('69',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('76',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('79',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('80',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['77','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('86',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k1_tops_1 @ X32 @ X31 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 @ ( k2_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88','91'])).

thf('93',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','94'])).

thf('96',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('97',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','82'])).

thf('100',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('102',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('104',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','82'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('107',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['77','81'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('113',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['111','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('119',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','117','118'])).

thf('120',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('121',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('123',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','117','118'])).

thf('125',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('127',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88','91'])).

thf('128',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('129',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('132',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('133',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['131','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['131','134'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('139',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('140',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('142',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('144',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','38','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['142','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X1 ) @ X0 @ k1_xboole_0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['137','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X1 @ k1_xboole_0 ) @ sk_B )
      | ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['136','146'])).

thf('148',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','147'])).

thf('149',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['126','129'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('151',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['130','151'])).

thf('153',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['111','116'])).

thf('155',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['125','153','154'])).

thf('156',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['55','155'])).

thf('157',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    $false ),
    inference(demod,[status(thm)],['40','157'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mLgOAatj80
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:14:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.81/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.81/1.01  % Solved by: fo/fo7.sh
% 0.81/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.01  % done 857 iterations in 0.584s
% 0.81/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.81/1.01  % SZS output start Refutation
% 0.81/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.81/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.81/1.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.81/1.01  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.81/1.01  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.81/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.81/1.01  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.81/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.81/1.01  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.81/1.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.81/1.01  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.81/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.81/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.81/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.81/1.01  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.81/1.01  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.81/1.01  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.81/1.01  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.81/1.01  thf(t76_tops_1, conjecture,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.81/1.01       ( ![B:$i]:
% 0.81/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.01           ( ( v3_pre_topc @ B @ A ) <=>
% 0.81/1.01             ( ( k2_tops_1 @ A @ B ) =
% 0.81/1.01               ( k7_subset_1 @
% 0.81/1.01                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.81/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.81/1.01    (~( ![A:$i]:
% 0.81/1.01        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.81/1.01          ( ![B:$i]:
% 0.81/1.01            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.01              ( ( v3_pre_topc @ B @ A ) <=>
% 0.81/1.01                ( ( k2_tops_1 @ A @ B ) =
% 0.81/1.01                  ( k7_subset_1 @
% 0.81/1.01                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.81/1.01    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.81/1.01  thf('0', plain,
% 0.81/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.81/1.01        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('1', plain,
% 0.81/1.01      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.81/1.01      inference('split', [status(esa)], ['0'])).
% 0.81/1.01  thf('2', plain,
% 0.81/1.01      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.81/1.01       ~
% 0.81/1.01       (((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.81/1.01      inference('split', [status(esa)], ['0'])).
% 0.81/1.01  thf('3', plain,
% 0.81/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.81/1.01        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('4', plain,
% 0.81/1.01      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.81/1.01      inference('split', [status(esa)], ['3'])).
% 0.81/1.01  thf('5', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(t55_tops_1, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.81/1.01       ( ![B:$i]:
% 0.81/1.01         ( ( l1_pre_topc @ B ) =>
% 0.81/1.01           ( ![C:$i]:
% 0.81/1.01             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.01               ( ![D:$i]:
% 0.81/1.01                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.81/1.01                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.81/1.01                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.81/1.01                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.81/1.01                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.81/1.01  thf('6', plain,
% 0.81/1.01      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.81/1.01         (~ (l1_pre_topc @ X27)
% 0.81/1.01          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.81/1.01          | ~ (v3_pre_topc @ X28 @ X27)
% 0.81/1.01          | ((k1_tops_1 @ X27 @ X28) = (X28))
% 0.81/1.01          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.81/1.01          | ~ (l1_pre_topc @ X30)
% 0.81/1.01          | ~ (v2_pre_topc @ X30))),
% 0.81/1.01      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.81/1.01  thf('7', plain,
% 0.81/1.01      ((![X27 : $i, X28 : $i]:
% 0.81/1.01          (~ (l1_pre_topc @ X27)
% 0.81/1.01           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.81/1.01           | ~ (v3_pre_topc @ X28 @ X27)
% 0.81/1.01           | ((k1_tops_1 @ X27 @ X28) = (X28))))
% 0.81/1.01         <= ((![X27 : $i, X28 : $i]:
% 0.81/1.01                (~ (l1_pre_topc @ X27)
% 0.81/1.01                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.81/1.01                 | ~ (v3_pre_topc @ X28 @ X27)
% 0.81/1.01                 | ((k1_tops_1 @ X27 @ X28) = (X28)))))),
% 0.81/1.01      inference('split', [status(esa)], ['6'])).
% 0.81/1.01  thf('8', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('9', plain,
% 0.81/1.01      ((![X29 : $i, X30 : $i]:
% 0.81/1.01          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.81/1.01           | ~ (l1_pre_topc @ X30)
% 0.81/1.01           | ~ (v2_pre_topc @ X30)))
% 0.81/1.01         <= ((![X29 : $i, X30 : $i]:
% 0.81/1.01                (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.81/1.01                 | ~ (l1_pre_topc @ X30)
% 0.81/1.01                 | ~ (v2_pre_topc @ X30))))),
% 0.81/1.01      inference('split', [status(esa)], ['6'])).
% 0.81/1.01  thf('10', plain,
% 0.81/1.01      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.81/1.01         <= ((![X29 : $i, X30 : $i]:
% 0.81/1.01                (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.81/1.01                 | ~ (l1_pre_topc @ X30)
% 0.81/1.01                 | ~ (v2_pre_topc @ X30))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['8', '9'])).
% 0.81/1.01  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('13', plain,
% 0.81/1.01      (~
% 0.81/1.01       (![X29 : $i, X30 : $i]:
% 0.81/1.01          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.81/1.01           | ~ (l1_pre_topc @ X30)
% 0.81/1.01           | ~ (v2_pre_topc @ X30)))),
% 0.81/1.01      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.81/1.01  thf('14', plain,
% 0.81/1.01      ((![X27 : $i, X28 : $i]:
% 0.81/1.01          (~ (l1_pre_topc @ X27)
% 0.81/1.01           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.81/1.01           | ~ (v3_pre_topc @ X28 @ X27)
% 0.81/1.01           | ((k1_tops_1 @ X27 @ X28) = (X28)))) | 
% 0.81/1.01       (![X29 : $i, X30 : $i]:
% 0.81/1.01          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.81/1.01           | ~ (l1_pre_topc @ X30)
% 0.81/1.01           | ~ (v2_pre_topc @ X30)))),
% 0.81/1.01      inference('split', [status(esa)], ['6'])).
% 0.81/1.01  thf('15', plain,
% 0.81/1.01      ((![X27 : $i, X28 : $i]:
% 0.81/1.01          (~ (l1_pre_topc @ X27)
% 0.81/1.01           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.81/1.01           | ~ (v3_pre_topc @ X28 @ X27)
% 0.81/1.01           | ((k1_tops_1 @ X27 @ X28) = (X28))))),
% 0.81/1.01      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 0.81/1.01  thf('16', plain,
% 0.81/1.01      (![X27 : $i, X28 : $i]:
% 0.81/1.01         (~ (l1_pre_topc @ X27)
% 0.81/1.01          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.81/1.01          | ~ (v3_pre_topc @ X28 @ X27)
% 0.81/1.01          | ((k1_tops_1 @ X27 @ X28) = (X28)))),
% 0.81/1.01      inference('simpl_trail', [status(thm)], ['7', '15'])).
% 0.81/1.01  thf('17', plain,
% 0.81/1.01      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.81/1.01        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.81/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['5', '16'])).
% 0.81/1.01  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('19', plain,
% 0.81/1.01      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.81/1.01      inference('demod', [status(thm)], ['17', '18'])).
% 0.81/1.01  thf('20', plain,
% 0.81/1.01      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.81/1.01         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['4', '19'])).
% 0.81/1.01  thf('21', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(l78_tops_1, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( l1_pre_topc @ A ) =>
% 0.81/1.01       ( ![B:$i]:
% 0.81/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.01           ( ( k2_tops_1 @ A @ B ) =
% 0.81/1.01             ( k7_subset_1 @
% 0.81/1.01               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.81/1.01               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.81/1.01  thf('22', plain,
% 0.81/1.01      (![X25 : $i, X26 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.81/1.01          | ((k2_tops_1 @ X26 @ X25)
% 0.81/1.01              = (k7_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.81/1.01                 (k2_pre_topc @ X26 @ X25) @ (k1_tops_1 @ X26 @ X25)))
% 0.81/1.01          | ~ (l1_pre_topc @ X26))),
% 0.81/1.01      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.81/1.01  thf('23', plain,
% 0.81/1.01      ((~ (l1_pre_topc @ sk_A)
% 0.81/1.01        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['21', '22'])).
% 0.81/1.01  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('25', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(dt_k2_pre_topc, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( ( l1_pre_topc @ A ) & 
% 0.81/1.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.81/1.01       ( m1_subset_1 @
% 0.81/1.01         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.81/1.01  thf('26', plain,
% 0.81/1.01      (![X23 : $i, X24 : $i]:
% 0.81/1.01         (~ (l1_pre_topc @ X23)
% 0.81/1.01          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.81/1.01          | (m1_subset_1 @ (k2_pre_topc @ X23 @ X24) @ 
% 0.81/1.01             (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 0.81/1.01      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.81/1.01  thf('27', plain,
% 0.81/1.01      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.81/1.01         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.81/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['25', '26'])).
% 0.81/1.01  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('29', plain,
% 0.81/1.01      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.81/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['27', '28'])).
% 0.81/1.01  thf(redefinition_k7_subset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.81/1.01       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.81/1.01  thf('30', plain,
% 0.81/1.01      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.81/1.01          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 0.81/1.01      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.81/1.01  thf('31', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.81/1.01           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['29', '30'])).
% 0.81/1.01  thf('32', plain,
% 0.81/1.01      (((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.81/1.01            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('demod', [status(thm)], ['23', '24', '31'])).
% 0.81/1.01  thf('33', plain,
% 0.81/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.81/1.01         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.81/1.01      inference('sup+', [status(thm)], ['20', '32'])).
% 0.81/1.01  thf('34', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.81/1.01           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['29', '30'])).
% 0.81/1.01  thf('35', plain,
% 0.81/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.81/1.01         <= (~
% 0.81/1.01             (((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.81/1.01      inference('split', [status(esa)], ['0'])).
% 0.81/1.01  thf('36', plain,
% 0.81/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.81/1.01         <= (~
% 0.81/1.01             (((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['34', '35'])).
% 0.81/1.01  thf('37', plain,
% 0.81/1.01      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.81/1.01         <= (~
% 0.81/1.01             (((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.81/1.01             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['33', '36'])).
% 0.81/1.01  thf('38', plain,
% 0.81/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.81/1.01       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.81/1.01      inference('simplify', [status(thm)], ['37'])).
% 0.81/1.01  thf('39', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.81/1.01      inference('sat_resolution*', [status(thm)], ['2', '38'])).
% 0.81/1.01  thf('40', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.81/1.01      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 0.81/1.01  thf('41', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('42', plain,
% 0.81/1.01      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.81/1.01         (~ (l1_pre_topc @ X27)
% 0.81/1.01          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.81/1.01          | ((k1_tops_1 @ X30 @ X29) != (X29))
% 0.81/1.01          | (v3_pre_topc @ X29 @ X30)
% 0.81/1.01          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.81/1.01          | ~ (l1_pre_topc @ X30)
% 0.81/1.01          | ~ (v2_pre_topc @ X30))),
% 0.81/1.01      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.81/1.01  thf('43', plain,
% 0.81/1.01      ((![X29 : $i, X30 : $i]:
% 0.81/1.01          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.81/1.01           | ~ (l1_pre_topc @ X30)
% 0.81/1.01           | ~ (v2_pre_topc @ X30)
% 0.81/1.01           | ((k1_tops_1 @ X30 @ X29) != (X29))
% 0.81/1.01           | (v3_pre_topc @ X29 @ X30)))
% 0.81/1.01         <= ((![X29 : $i, X30 : $i]:
% 0.81/1.01                (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.81/1.01                 | ~ (l1_pre_topc @ X30)
% 0.81/1.01                 | ~ (v2_pre_topc @ X30)
% 0.81/1.01                 | ((k1_tops_1 @ X30 @ X29) != (X29))
% 0.81/1.01                 | (v3_pre_topc @ X29 @ X30))))),
% 0.81/1.01      inference('split', [status(esa)], ['42'])).
% 0.81/1.01  thf('44', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('45', plain,
% 0.81/1.01      ((![X27 : $i, X28 : $i]:
% 0.81/1.01          (~ (l1_pre_topc @ X27)
% 0.81/1.01           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))))
% 0.81/1.01         <= ((![X27 : $i, X28 : $i]:
% 0.81/1.01                (~ (l1_pre_topc @ X27)
% 0.81/1.01                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))))),
% 0.81/1.01      inference('split', [status(esa)], ['42'])).
% 0.81/1.01  thf('46', plain,
% 0.81/1.01      ((~ (l1_pre_topc @ sk_A))
% 0.81/1.01         <= ((![X27 : $i, X28 : $i]:
% 0.81/1.01                (~ (l1_pre_topc @ X27)
% 0.81/1.01                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['44', '45'])).
% 0.81/1.01  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('48', plain,
% 0.81/1.01      (~
% 0.81/1.01       (![X27 : $i, X28 : $i]:
% 0.81/1.01          (~ (l1_pre_topc @ X27)
% 0.81/1.01           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))))),
% 0.81/1.01      inference('demod', [status(thm)], ['46', '47'])).
% 0.81/1.01  thf('49', plain,
% 0.81/1.01      ((![X29 : $i, X30 : $i]:
% 0.81/1.01          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.81/1.01           | ~ (l1_pre_topc @ X30)
% 0.81/1.01           | ~ (v2_pre_topc @ X30)
% 0.81/1.01           | ((k1_tops_1 @ X30 @ X29) != (X29))
% 0.81/1.01           | (v3_pre_topc @ X29 @ X30))) | 
% 0.81/1.01       (![X27 : $i, X28 : $i]:
% 0.81/1.01          (~ (l1_pre_topc @ X27)
% 0.81/1.01           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))))),
% 0.81/1.01      inference('split', [status(esa)], ['42'])).
% 0.81/1.01  thf('50', plain,
% 0.81/1.01      ((![X29 : $i, X30 : $i]:
% 0.81/1.01          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.81/1.01           | ~ (l1_pre_topc @ X30)
% 0.81/1.01           | ~ (v2_pre_topc @ X30)
% 0.81/1.01           | ((k1_tops_1 @ X30 @ X29) != (X29))
% 0.81/1.01           | (v3_pre_topc @ X29 @ X30)))),
% 0.81/1.01      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.81/1.01  thf('51', plain,
% 0.81/1.01      (![X29 : $i, X30 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.81/1.01          | ~ (l1_pre_topc @ X30)
% 0.81/1.01          | ~ (v2_pre_topc @ X30)
% 0.81/1.01          | ((k1_tops_1 @ X30 @ X29) != (X29))
% 0.81/1.01          | (v3_pre_topc @ X29 @ X30))),
% 0.81/1.01      inference('simpl_trail', [status(thm)], ['43', '50'])).
% 0.81/1.01  thf('52', plain,
% 0.81/1.01      (((v3_pre_topc @ sk_B @ sk_A)
% 0.81/1.01        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 0.81/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.81/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['41', '51'])).
% 0.81/1.01  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('55', plain,
% 0.81/1.01      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 0.81/1.01      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.81/1.01  thf(d5_xboole_0, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.81/1.01       ( ![D:$i]:
% 0.81/1.01         ( ( r2_hidden @ D @ C ) <=>
% 0.81/1.01           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.81/1.01  thf('56', plain,
% 0.81/1.01      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.81/1.01         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.81/1.01          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.81/1.01          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.81/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.81/1.01  thf(commutativity_k3_xboole_0, axiom,
% 0.81/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.81/1.01  thf('57', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.81/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.81/1.01  thf(t2_boole, axiom,
% 0.81/1.01    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.81/1.01  thf('58', plain,
% 0.81/1.01      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/1.01      inference('cnf', [status(esa)], [t2_boole])).
% 0.81/1.01  thf('59', plain,
% 0.81/1.01      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['57', '58'])).
% 0.81/1.01  thf(t100_xboole_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.81/1.01  thf('60', plain,
% 0.81/1.01      (![X11 : $i, X12 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ X11 @ X12)
% 0.81/1.01           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.81/1.01  thf('61', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.81/1.01           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['59', '60'])).
% 0.81/1.01  thf(t48_xboole_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.81/1.01  thf('62', plain,
% 0.81/1.01      (![X16 : $i, X17 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.81/1.01           = (k3_xboole_0 @ X16 @ X17))),
% 0.81/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/1.01  thf('63', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ k1_xboole_0 @ 
% 0.81/1.01           (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.81/1.01           = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['61', '62'])).
% 0.81/1.01  thf('64', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.81/1.01           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['59', '60'])).
% 0.81/1.01  thf('65', plain,
% 0.81/1.01      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['57', '58'])).
% 0.81/1.01  thf('66', plain,
% 0.81/1.01      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/1.01      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.81/1.01  thf(d10_xboole_0, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.81/1.01  thf('67', plain,
% 0.81/1.01      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.81/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.01  thf('68', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.81/1.01      inference('simplify', [status(thm)], ['67'])).
% 0.81/1.01  thf(t28_xboole_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.81/1.01  thf('69', plain,
% 0.81/1.01      (![X13 : $i, X14 : $i]:
% 0.81/1.01         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.81/1.01      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.81/1.01  thf('70', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['68', '69'])).
% 0.81/1.01  thf('71', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.81/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.81/1.01  thf('72', plain,
% 0.81/1.01      (![X11 : $i, X12 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ X11 @ X12)
% 0.81/1.01           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.81/1.01  thf('73', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ X0 @ X1)
% 0.81/1.01           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.81/1.01      inference('sup+', [status(thm)], ['71', '72'])).
% 0.81/1.01  thf('74', plain,
% 0.81/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['70', '73'])).
% 0.81/1.01  thf('75', plain,
% 0.81/1.01      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.81/1.01         (~ (r2_hidden @ X6 @ X5)
% 0.81/1.01          | (r2_hidden @ X6 @ X3)
% 0.81/1.01          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.81/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.81/1.01  thf('76', plain,
% 0.81/1.01      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.81/1.01         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.81/1.01      inference('simplify', [status(thm)], ['75'])).
% 0.81/1.01  thf('77', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['74', '76'])).
% 0.81/1.01  thf('78', plain,
% 0.81/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['70', '73'])).
% 0.81/1.01  thf('79', plain,
% 0.81/1.01      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.81/1.01         (~ (r2_hidden @ X6 @ X5)
% 0.81/1.01          | ~ (r2_hidden @ X6 @ X4)
% 0.81/1.01          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.81/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.81/1.01  thf('80', plain,
% 0.81/1.01      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.81/1.01         (~ (r2_hidden @ X6 @ X4)
% 0.81/1.01          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.81/1.01      inference('simplify', [status(thm)], ['79'])).
% 0.81/1.01  thf('81', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.81/1.01          | ~ (r2_hidden @ X1 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['78', '80'])).
% 0.81/1.01  thf('82', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.01      inference('clc', [status(thm)], ['77', '81'])).
% 0.81/1.01  thf('83', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.81/1.01      inference('sup-', [status(thm)], ['66', '82'])).
% 0.81/1.01  thf('84', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.81/1.01          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['56', '83'])).
% 0.81/1.01  thf('85', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(t74_tops_1, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( l1_pre_topc @ A ) =>
% 0.81/1.01       ( ![B:$i]:
% 0.81/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.01           ( ( k1_tops_1 @ A @ B ) =
% 0.81/1.01             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.81/1.01  thf('86', plain,
% 0.81/1.01      (![X31 : $i, X32 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.81/1.01          | ((k1_tops_1 @ X32 @ X31)
% 0.81/1.01              = (k7_subset_1 @ (u1_struct_0 @ X32) @ X31 @ 
% 0.81/1.01                 (k2_tops_1 @ X32 @ X31)))
% 0.81/1.01          | ~ (l1_pre_topc @ X32))),
% 0.81/1.01      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.81/1.01  thf('87', plain,
% 0.81/1.01      ((~ (l1_pre_topc @ sk_A)
% 0.81/1.01        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.01            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.81/1.01               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['85', '86'])).
% 0.81/1.01  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('89', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('90', plain,
% 0.81/1.01      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.81/1.01          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 0.81/1.01      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.81/1.01  thf('91', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.81/1.01           = (k4_xboole_0 @ sk_B @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['89', '90'])).
% 0.81/1.01  thf('92', plain,
% 0.81/1.01      (((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.01         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('demod', [status(thm)], ['87', '88', '91'])).
% 0.81/1.01  thf('93', plain,
% 0.81/1.01      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.81/1.01         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.81/1.01      inference('simplify', [status(thm)], ['75'])).
% 0.81/1.01  thf('94', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         (~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.81/1.01          | (r2_hidden @ X0 @ sk_B))),
% 0.81/1.01      inference('sup-', [status(thm)], ['92', '93'])).
% 0.81/1.01  thf('95', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         (((k1_xboole_0) = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 0.81/1.01          | (r2_hidden @ 
% 0.81/1.01             (sk_D @ k1_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B))),
% 0.81/1.01      inference('sup-', [status(thm)], ['84', '94'])).
% 0.81/1.01  thf('96', plain,
% 0.81/1.01      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.81/1.01         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.81/1.01          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.81/1.01          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.81/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.81/1.01  thf('97', plain,
% 0.81/1.01      ((((k1_xboole_0) = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.81/1.01        | (r2_hidden @ 
% 0.81/1.01           (sk_D @ k1_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.81/1.01           k1_xboole_0)
% 0.81/1.01        | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['95', '96'])).
% 0.81/1.01  thf('98', plain,
% 0.81/1.01      (((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.81/1.01         k1_xboole_0)
% 0.81/1.01        | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.81/1.01      inference('simplify', [status(thm)], ['97'])).
% 0.81/1.01  thf('99', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.81/1.01      inference('sup-', [status(thm)], ['66', '82'])).
% 0.81/1.01  thf('100', plain,
% 0.81/1.01      (((k1_xboole_0) = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.81/1.01      inference('clc', [status(thm)], ['98', '99'])).
% 0.81/1.01  thf('101', plain,
% 0.81/1.01      (![X16 : $i, X17 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.81/1.01           = (k3_xboole_0 @ X16 @ X17))),
% 0.81/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/1.01  thf('102', plain,
% 0.81/1.01      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.81/1.01         = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.81/1.01      inference('sup+', [status(thm)], ['100', '101'])).
% 0.81/1.01  thf('103', plain,
% 0.81/1.01      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.81/1.01         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.81/1.01          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.81/1.01          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.81/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.81/1.01  thf('104', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.81/1.01      inference('sup-', [status(thm)], ['66', '82'])).
% 0.81/1.01  thf('105', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.81/1.01          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['103', '104'])).
% 0.81/1.01  thf('106', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.81/1.01           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['59', '60'])).
% 0.81/1.01  thf('107', plain,
% 0.81/1.01      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/1.01      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.81/1.01  thf('108', plain,
% 0.81/1.01      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.81/1.01      inference('demod', [status(thm)], ['106', '107'])).
% 0.81/1.01  thf('109', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.81/1.01          | ((X1) = (k1_xboole_0)))),
% 0.81/1.01      inference('demod', [status(thm)], ['105', '108'])).
% 0.81/1.01  thf('110', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.01      inference('clc', [status(thm)], ['77', '81'])).
% 0.81/1.01  thf('111', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['109', '110'])).
% 0.81/1.01  thf('112', plain,
% 0.81/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['70', '73'])).
% 0.81/1.01  thf('113', plain,
% 0.81/1.01      (![X16 : $i, X17 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.81/1.01           = (k3_xboole_0 @ X16 @ X17))),
% 0.81/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/1.01  thf('114', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.81/1.01           = (k3_xboole_0 @ X0 @ X0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['112', '113'])).
% 0.81/1.01  thf('115', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['68', '69'])).
% 0.81/1.01  thf('116', plain,
% 0.81/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.81/1.01      inference('demod', [status(thm)], ['114', '115'])).
% 0.81/1.01  thf('117', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['111', '116'])).
% 0.81/1.01  thf('118', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.81/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.81/1.01  thf('119', plain,
% 0.81/1.01      (((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.01         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('demod', [status(thm)], ['102', '117', '118'])).
% 0.81/1.01  thf('120', plain,
% 0.81/1.01      (![X11 : $i, X12 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ X11 @ X12)
% 0.81/1.01           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.81/1.01  thf('121', plain,
% 0.81/1.01      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.81/1.01         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('sup+', [status(thm)], ['119', '120'])).
% 0.81/1.01  thf('122', plain,
% 0.81/1.01      (![X16 : $i, X17 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.81/1.01           = (k3_xboole_0 @ X16 @ X17))),
% 0.81/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/1.01  thf('123', plain,
% 0.81/1.01      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.81/1.01         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('sup+', [status(thm)], ['121', '122'])).
% 0.81/1.01  thf('124', plain,
% 0.81/1.01      (((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.01         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('demod', [status(thm)], ['102', '117', '118'])).
% 0.81/1.01  thf('125', plain,
% 0.81/1.01      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.81/1.01         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.81/1.01      inference('demod', [status(thm)], ['123', '124'])).
% 0.81/1.01  thf('126', plain,
% 0.81/1.01      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.81/1.01         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('sup+', [status(thm)], ['119', '120'])).
% 0.81/1.01  thf('127', plain,
% 0.81/1.01      (((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.01         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('demod', [status(thm)], ['87', '88', '91'])).
% 0.81/1.01  thf('128', plain,
% 0.81/1.01      (![X16 : $i, X17 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.81/1.01           = (k3_xboole_0 @ X16 @ X17))),
% 0.81/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/1.01  thf('129', plain,
% 0.81/1.01      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.81/1.01         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('sup+', [status(thm)], ['127', '128'])).
% 0.81/1.01  thf('130', plain,
% 0.81/1.01      (((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.81/1.01         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('sup+', [status(thm)], ['126', '129'])).
% 0.81/1.01  thf('131', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.81/1.01          | ((X1) = (k1_xboole_0)))),
% 0.81/1.01      inference('demod', [status(thm)], ['105', '108'])).
% 0.81/1.01  thf('132', plain,
% 0.81/1.01      (![X16 : $i, X17 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.81/1.01           = (k3_xboole_0 @ X16 @ X17))),
% 0.81/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/1.01  thf('133', plain,
% 0.81/1.01      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.81/1.01         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.81/1.01      inference('simplify', [status(thm)], ['75'])).
% 0.81/1.01  thf('134', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.01         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.81/1.01      inference('sup-', [status(thm)], ['132', '133'])).
% 0.81/1.01  thf('135', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.01         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.81/1.01          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 0.81/1.01             X1))),
% 0.81/1.01      inference('sup-', [status(thm)], ['131', '134'])).
% 0.81/1.01  thf('136', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.81/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.81/1.01  thf('137', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.01         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.81/1.01          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 0.81/1.01             X1))),
% 0.81/1.01      inference('sup-', [status(thm)], ['131', '134'])).
% 0.81/1.01  thf('138', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.81/1.01           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['29', '30'])).
% 0.81/1.01  thf('139', plain,
% 0.81/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.81/1.01         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.81/1.01      inference('split', [status(esa)], ['3'])).
% 0.81/1.01  thf('140', plain,
% 0.81/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.81/1.01         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.81/1.01      inference('sup+', [status(thm)], ['138', '139'])).
% 0.81/1.01  thf('141', plain,
% 0.81/1.01      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.81/1.01         (~ (r2_hidden @ X6 @ X4)
% 0.81/1.01          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.81/1.01      inference('simplify', [status(thm)], ['79'])).
% 0.81/1.01  thf('142', plain,
% 0.81/1.01      ((![X0 : $i]:
% 0.81/1.01          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.81/1.01           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.81/1.01         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['140', '141'])).
% 0.81/1.01  thf('143', plain,
% 0.81/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.81/1.01       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.81/1.01      inference('split', [status(esa)], ['3'])).
% 0.81/1.01  thf('144', plain,
% 0.81/1.01      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.81/1.01      inference('sat_resolution*', [status(thm)], ['2', '38', '143'])).
% 0.81/1.01  thf('145', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.81/1.01          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.81/1.01      inference('simpl_trail', [status(thm)], ['142', '144'])).
% 0.81/1.01  thf('146', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X1) = (k1_xboole_0))
% 0.81/1.01          | ~ (r2_hidden @ 
% 0.81/1.01               (sk_D @ (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X1) @ X0 @ 
% 0.81/1.01                k1_xboole_0) @ 
% 0.81/1.01               sk_B))),
% 0.81/1.01      inference('sup-', [status(thm)], ['137', '145'])).
% 0.81/1.01  thf('147', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (~ (r2_hidden @ 
% 0.81/1.01             (sk_D @ (k3_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ X1 @ 
% 0.81/1.01              k1_xboole_0) @ 
% 0.81/1.01             sk_B)
% 0.81/1.01          | ((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) = (k1_xboole_0)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['136', '146'])).
% 0.81/1.01  thf('148', plain,
% 0.81/1.01      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.81/1.01        | ((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['135', '147'])).
% 0.81/1.01  thf('149', plain,
% 0.81/1.01      (((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.81/1.01         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('sup+', [status(thm)], ['126', '129'])).
% 0.81/1.01  thf('150', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.81/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.81/1.01  thf('151', plain,
% 0.81/1.01      ((((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.81/1.01        | ((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 0.81/1.01      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.81/1.01  thf('152', plain,
% 0.81/1.01      ((((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.81/1.01        | ((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 0.81/1.01      inference('sup+', [status(thm)], ['130', '151'])).
% 0.81/1.01  thf('153', plain,
% 0.81/1.01      (((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.81/1.01      inference('simplify', [status(thm)], ['152'])).
% 0.81/1.01  thf('154', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['111', '116'])).
% 0.81/1.01  thf('155', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 0.81/1.01      inference('demod', [status(thm)], ['125', '153', '154'])).
% 0.81/1.01  thf('156', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.81/1.01      inference('demod', [status(thm)], ['55', '155'])).
% 0.81/1.01  thf('157', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.81/1.01      inference('simplify', [status(thm)], ['156'])).
% 0.81/1.01  thf('158', plain, ($false), inference('demod', [status(thm)], ['40', '157'])).
% 0.81/1.01  
% 0.81/1.01  % SZS output end Refutation
% 0.81/1.01  
% 0.81/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
