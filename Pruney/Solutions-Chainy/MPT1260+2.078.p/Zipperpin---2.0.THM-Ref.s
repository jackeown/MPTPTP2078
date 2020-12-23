%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qI9RvBhPNs

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:35 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 282 expanded)
%              Number of leaves         :   22 (  84 expanded)
%              Depth                    :   21
%              Number of atoms          : 1178 (4316 expanded)
%              Number of equality atoms :   71 ( 219 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( ( k1_tops_1 @ X24 @ X25 )
        = X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('7',plain,
    ( ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( v3_pre_topc @ X25 @ X24 )
        | ( ( k1_tops_1 @ X24 @ X25 )
          = X25 ) )
   <= ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( v3_pre_topc @ X25 @ X24 )
        | ( ( k1_tops_1 @ X24 @ X25 )
          = X25 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) )
   <= ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( v3_pre_topc @ X25 @ X24 )
        | ( ( k1_tops_1 @ X24 @ X25 )
          = X25 ) )
    | ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( ( k1_tops_1 @ X24 @ X25 )
        = X25 ) ) ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( ( k1_tops_1 @ X24 @ X25 )
        = X25 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k2_tops_1 @ X23 @ X22 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k2_pre_topc @ X23 @ X22 ) @ ( k1_tops_1 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k1_tops_1 @ X27 @ X26 )
       != X26 )
      | ( v3_pre_topc @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('43',plain,
    ( ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 )
        | ( ( k1_tops_1 @ X27 @ X26 )
         != X26 )
        | ( v3_pre_topc @ X26 @ X27 ) )
   <= ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 )
        | ( ( k1_tops_1 @ X27 @ X26 )
         != X26 )
        | ( v3_pre_topc @ X26 @ X27 ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
   <= ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 )
        | ( ( k1_tops_1 @ X27 @ X26 )
         != X26 )
        | ( v3_pre_topc @ X26 @ X27 ) )
    | ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('50',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( ( k1_tops_1 @ X27 @ X26 )
       != X26 )
      | ( v3_pre_topc @ X26 @ X27 ) ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( ( k1_tops_1 @ X27 @ X26 )
       != X26 )
      | ( v3_pre_topc @ X26 @ X27 ) ) ),
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
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['56'])).

thf('59',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['56'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('65',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('66',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('68',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('71',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','38','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','73'])).

thf('75',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('77',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k1_tops_1 @ X29 @ X28 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 @ ( k2_tops_1 @ X29 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79','82'])).

thf('84',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['75','83'])).

thf('85',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['55','84'])).

thf('86',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['40','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qI9RvBhPNs
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:05:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 234 iterations in 0.179s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.46/0.63  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.46/0.63  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.63  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.63  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.63  thf(t76_tops_1, conjecture,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( ( v3_pre_topc @ B @ A ) <=>
% 0.46/0.63             ( ( k2_tops_1 @ A @ B ) =
% 0.46/0.63               ( k7_subset_1 @
% 0.46/0.63                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]:
% 0.46/0.63        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63          ( ![B:$i]:
% 0.46/0.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63              ( ( v3_pre_topc @ B @ A ) <=>
% 0.46/0.63                ( ( k2_tops_1 @ A @ B ) =
% 0.46/0.63                  ( k7_subset_1 @
% 0.46/0.63                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.46/0.63        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.63      inference('split', [status(esa)], ['0'])).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.46/0.63       ~
% 0.46/0.63       (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.46/0.63      inference('split', [status(esa)], ['0'])).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.46/0.63        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.63      inference('split', [status(esa)], ['3'])).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t55_tops_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( l1_pre_topc @ B ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63               ( ![D:$i]:
% 0.46/0.63                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.63                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.46/0.63                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.46/0.63                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.46/0.63                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X24)
% 0.46/0.63          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.46/0.63          | ~ (v3_pre_topc @ X25 @ X24)
% 0.46/0.63          | ((k1_tops_1 @ X24 @ X25) = (X25))
% 0.46/0.63          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.63          | ~ (l1_pre_topc @ X27)
% 0.46/0.63          | ~ (v2_pre_topc @ X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      ((![X24 : $i, X25 : $i]:
% 0.46/0.63          (~ (l1_pre_topc @ X24)
% 0.46/0.63           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.46/0.63           | ~ (v3_pre_topc @ X25 @ X24)
% 0.46/0.63           | ((k1_tops_1 @ X24 @ X25) = (X25))))
% 0.46/0.63         <= ((![X24 : $i, X25 : $i]:
% 0.46/0.63                (~ (l1_pre_topc @ X24)
% 0.46/0.63                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.46/0.63                 | ~ (v3_pre_topc @ X25 @ X24)
% 0.46/0.63                 | ((k1_tops_1 @ X24 @ X25) = (X25)))))),
% 0.46/0.63      inference('split', [status(esa)], ['6'])).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      ((![X26 : $i, X27 : $i]:
% 0.46/0.63          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.63           | ~ (l1_pre_topc @ X27)
% 0.46/0.63           | ~ (v2_pre_topc @ X27)))
% 0.46/0.63         <= ((![X26 : $i, X27 : $i]:
% 0.46/0.63                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.63                 | ~ (l1_pre_topc @ X27)
% 0.46/0.63                 | ~ (v2_pre_topc @ X27))))),
% 0.46/0.63      inference('split', [status(esa)], ['6'])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.46/0.63         <= ((![X26 : $i, X27 : $i]:
% 0.46/0.63                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.63                 | ~ (l1_pre_topc @ X27)
% 0.46/0.63                 | ~ (v2_pre_topc @ X27))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.63  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      (~
% 0.46/0.63       (![X26 : $i, X27 : $i]:
% 0.46/0.63          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.63           | ~ (l1_pre_topc @ X27)
% 0.46/0.63           | ~ (v2_pre_topc @ X27)))),
% 0.46/0.63      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      ((![X24 : $i, X25 : $i]:
% 0.46/0.63          (~ (l1_pre_topc @ X24)
% 0.46/0.63           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.46/0.63           | ~ (v3_pre_topc @ X25 @ X24)
% 0.46/0.63           | ((k1_tops_1 @ X24 @ X25) = (X25)))) | 
% 0.46/0.63       (![X26 : $i, X27 : $i]:
% 0.46/0.63          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.63           | ~ (l1_pre_topc @ X27)
% 0.46/0.63           | ~ (v2_pre_topc @ X27)))),
% 0.46/0.63      inference('split', [status(esa)], ['6'])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      ((![X24 : $i, X25 : $i]:
% 0.46/0.63          (~ (l1_pre_topc @ X24)
% 0.46/0.63           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.46/0.63           | ~ (v3_pre_topc @ X25 @ X24)
% 0.46/0.63           | ((k1_tops_1 @ X24 @ X25) = (X25))))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (![X24 : $i, X25 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X24)
% 0.46/0.63          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.46/0.63          | ~ (v3_pre_topc @ X25 @ X24)
% 0.46/0.63          | ((k1_tops_1 @ X24 @ X25) = (X25)))),
% 0.46/0.63      inference('simpl_trail', [status(thm)], ['7', '15'])).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.46/0.63        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['5', '16'])).
% 0.46/0.63  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.46/0.63         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['4', '19'])).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(l78_tops_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( ( k2_tops_1 @ A @ B ) =
% 0.46/0.63             ( k7_subset_1 @
% 0.46/0.63               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.46/0.63               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (![X22 : $i, X23 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.46/0.63          | ((k2_tops_1 @ X23 @ X22)
% 0.46/0.63              = (k7_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.46/0.63                 (k2_pre_topc @ X23 @ X22) @ (k1_tops_1 @ X23 @ X22)))
% 0.46/0.63          | ~ (l1_pre_topc @ X23))),
% 0.46/0.63      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.63  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(dt_k2_pre_topc, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63       ( m1_subset_1 @
% 0.46/0.63         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (![X20 : $i, X21 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X20)
% 0.46/0.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.63          | (m1_subset_1 @ (k2_pre_topc @ X20 @ X21) @ 
% 0.46/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.46/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.63  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.63  thf(redefinition_k7_subset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.63       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.46/0.63  thf('30', plain,
% 0.46/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.46/0.63          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.46/0.63           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('32', plain,
% 0.46/0.63      (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.46/0.63            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['23', '24', '31'])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.46/0.63         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['20', '32'])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.46/0.63           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('35', plain,
% 0.46/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.46/0.63         <= (~
% 0.46/0.63             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.46/0.63      inference('split', [status(esa)], ['0'])).
% 0.46/0.63  thf('36', plain,
% 0.46/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.46/0.63         <= (~
% 0.46/0.63             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.46/0.63         <= (~
% 0.46/0.63             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.46/0.63             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['33', '36'])).
% 0.46/0.63  thf('38', plain,
% 0.46/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.46/0.63       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.46/0.63      inference('simplify', [status(thm)], ['37'])).
% 0.46/0.63  thf('39', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['2', '38'])).
% 0.46/0.63  thf('40', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 0.46/0.63  thf('41', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X24)
% 0.46/0.63          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.46/0.63          | ((k1_tops_1 @ X27 @ X26) != (X26))
% 0.46/0.63          | (v3_pre_topc @ X26 @ X27)
% 0.46/0.63          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.63          | ~ (l1_pre_topc @ X27)
% 0.46/0.63          | ~ (v2_pre_topc @ X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.46/0.63  thf('43', plain,
% 0.46/0.63      ((![X26 : $i, X27 : $i]:
% 0.46/0.63          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.63           | ~ (l1_pre_topc @ X27)
% 0.46/0.63           | ~ (v2_pre_topc @ X27)
% 0.46/0.63           | ((k1_tops_1 @ X27 @ X26) != (X26))
% 0.46/0.63           | (v3_pre_topc @ X26 @ X27)))
% 0.46/0.63         <= ((![X26 : $i, X27 : $i]:
% 0.46/0.63                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.63                 | ~ (l1_pre_topc @ X27)
% 0.46/0.63                 | ~ (v2_pre_topc @ X27)
% 0.46/0.63                 | ((k1_tops_1 @ X27 @ X26) != (X26))
% 0.46/0.63                 | (v3_pre_topc @ X26 @ X27))))),
% 0.46/0.63      inference('split', [status(esa)], ['42'])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('45', plain,
% 0.46/0.63      ((![X24 : $i, X25 : $i]:
% 0.46/0.63          (~ (l1_pre_topc @ X24)
% 0.46/0.63           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))))
% 0.46/0.63         <= ((![X24 : $i, X25 : $i]:
% 0.46/0.63                (~ (l1_pre_topc @ X24)
% 0.46/0.63                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))))),
% 0.46/0.63      inference('split', [status(esa)], ['42'])).
% 0.46/0.63  thf('46', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A))
% 0.46/0.63         <= ((![X24 : $i, X25 : $i]:
% 0.46/0.63                (~ (l1_pre_topc @ X24)
% 0.46/0.63                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.63  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      (~
% 0.46/0.63       (![X24 : $i, X25 : $i]:
% 0.46/0.63          (~ (l1_pre_topc @ X24)
% 0.46/0.63           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))))),
% 0.46/0.63      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.63  thf('49', plain,
% 0.46/0.63      ((![X26 : $i, X27 : $i]:
% 0.46/0.63          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.63           | ~ (l1_pre_topc @ X27)
% 0.46/0.63           | ~ (v2_pre_topc @ X27)
% 0.46/0.63           | ((k1_tops_1 @ X27 @ X26) != (X26))
% 0.46/0.63           | (v3_pre_topc @ X26 @ X27))) | 
% 0.46/0.63       (![X24 : $i, X25 : $i]:
% 0.46/0.63          (~ (l1_pre_topc @ X24)
% 0.46/0.63           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))))),
% 0.46/0.63      inference('split', [status(esa)], ['42'])).
% 0.46/0.63  thf('50', plain,
% 0.46/0.63      ((![X26 : $i, X27 : $i]:
% 0.46/0.63          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.63           | ~ (l1_pre_topc @ X27)
% 0.46/0.63           | ~ (v2_pre_topc @ X27)
% 0.46/0.63           | ((k1_tops_1 @ X27 @ X26) != (X26))
% 0.46/0.63           | (v3_pre_topc @ X26 @ X27)))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      (![X26 : $i, X27 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.63          | ~ (l1_pre_topc @ X27)
% 0.46/0.63          | ~ (v2_pre_topc @ X27)
% 0.46/0.63          | ((k1_tops_1 @ X27 @ X26) != (X26))
% 0.46/0.63          | (v3_pre_topc @ X26 @ X27))),
% 0.46/0.63      inference('simpl_trail', [status(thm)], ['43', '50'])).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      (((v3_pre_topc @ sk_B @ sk_A)
% 0.46/0.63        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 0.46/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['41', '51'])).
% 0.46/0.63  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('55', plain,
% 0.46/0.63      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.46/0.63  thf(d5_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.46/0.63       ( ![D:$i]:
% 0.46/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.63           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.46/0.63  thf('56', plain,
% 0.46/0.63      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.46/0.63         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 0.46/0.63          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 0.46/0.63          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.63  thf('57', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X0)
% 0.46/0.63          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.63      inference('eq_fact', [status(thm)], ['56'])).
% 0.46/0.63  thf('58', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X0)
% 0.46/0.63          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.63      inference('eq_fact', [status(thm)], ['56'])).
% 0.46/0.63  thf('59', plain,
% 0.46/0.63      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.46/0.63         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 0.46/0.63          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X8)
% 0.46/0.63          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 0.46/0.63          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.63  thf('60', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.46/0.63          | ~ (r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X0)
% 0.46/0.63          | (r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X1)
% 0.46/0.63          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.63  thf('61', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X1)
% 0.46/0.63          | ~ (r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X0)
% 0.46/0.63          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['60'])).
% 0.46/0.63  thf('62', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X0)
% 0.46/0.63          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.63      inference('eq_fact', [status(thm)], ['56'])).
% 0.46/0.63  thf('63', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.46/0.63          | (r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X1))),
% 0.46/0.63      inference('clc', [status(thm)], ['61', '62'])).
% 0.46/0.63  thf('64', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.46/0.63           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('65', plain,
% 0.46/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.46/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.46/0.63      inference('split', [status(esa)], ['3'])).
% 0.46/0.63  thf('66', plain,
% 0.46/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.46/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.46/0.63      inference('sup+', [status(thm)], ['64', '65'])).
% 0.46/0.63  thf('67', plain,
% 0.46/0.63      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X10 @ X9)
% 0.46/0.63          | ~ (r2_hidden @ X10 @ X8)
% 0.46/0.63          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.63  thf('68', plain,
% 0.46/0.63      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X10 @ X8)
% 0.46/0.63          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['67'])).
% 0.46/0.63  thf('69', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.46/0.63           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.46/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['66', '68'])).
% 0.46/0.63  thf('70', plain,
% 0.46/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.46/0.63       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.46/0.63      inference('split', [status(esa)], ['3'])).
% 0.46/0.63  thf('71', plain,
% 0.46/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['2', '38', '70'])).
% 0.46/0.63  thf('72', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.46/0.63          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.46/0.63      inference('simpl_trail', [status(thm)], ['69', '71'])).
% 0.46/0.63  thf('73', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((X0) = (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.46/0.63          | ~ (r2_hidden @ (sk_D_1 @ X0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 0.46/0.63               sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['63', '72'])).
% 0.46/0.63  thf('74', plain,
% 0.46/0.63      ((((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.46/0.63        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['57', '73'])).
% 0.46/0.63  thf('75', plain,
% 0.46/0.63      (((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['74'])).
% 0.46/0.63  thf('76', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t74_tops_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( ( k1_tops_1 @ A @ B ) =
% 0.46/0.63             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.63  thf('77', plain,
% 0.46/0.63      (![X28 : $i, X29 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.46/0.63          | ((k1_tops_1 @ X29 @ X28)
% 0.46/0.63              = (k7_subset_1 @ (u1_struct_0 @ X29) @ X28 @ 
% 0.46/0.63                 (k2_tops_1 @ X29 @ X28)))
% 0.46/0.63          | ~ (l1_pre_topc @ X29))),
% 0.46/0.63      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.46/0.63  thf('78', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.46/0.63            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.63               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['76', '77'])).
% 0.46/0.63  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('80', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('81', plain,
% 0.46/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.46/0.63          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.46/0.63  thf('82', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.46/0.63           = (k4_xboole_0 @ sk_B @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['80', '81'])).
% 0.46/0.63  thf('83', plain,
% 0.46/0.63      (((k1_tops_1 @ sk_A @ sk_B)
% 0.46/0.63         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['78', '79', '82'])).
% 0.46/0.63  thf('84', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['75', '83'])).
% 0.46/0.63  thf('85', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['55', '84'])).
% 0.46/0.63  thf('86', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('simplify', [status(thm)], ['85'])).
% 0.46/0.63  thf('87', plain, ($false), inference('demod', [status(thm)], ['40', '86'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
