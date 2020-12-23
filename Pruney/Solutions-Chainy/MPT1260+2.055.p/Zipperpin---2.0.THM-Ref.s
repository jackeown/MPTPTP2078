%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zUBqN1QsRU

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:31 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  217 (1002 expanded)
%              Number of leaves         :   31 ( 299 expanded)
%              Depth                    :   24
%              Number of atoms          : 2078 (12175 expanded)
%              Number of equality atoms :  152 ( 803 expanded)
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

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X28 )
      | ( ( k1_tops_1 @ X28 @ X29 )
        = X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('7',plain,
    ( ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( v3_pre_topc @ X29 @ X28 )
        | ( ( k1_tops_1 @ X28 @ X29 )
          = X29 ) )
   <= ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( v3_pre_topc @ X29 @ X28 )
        | ( ( k1_tops_1 @ X28 @ X29 )
          = X29 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 ) )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( v3_pre_topc @ X29 @ X28 )
        | ( ( k1_tops_1 @ X28 @ X29 )
          = X29 ) )
    | ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X28 )
      | ( ( k1_tops_1 @ X28 @ X29 )
        = X29 ) ) ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X28 )
      | ( ( k1_tops_1 @ X28 @ X29 )
        = X29 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k2_tops_1 @ X27 @ X26 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k2_pre_topc @ X27 @ X26 ) @ ( k1_tops_1 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k1_tops_1 @ X31 @ X30 )
       != X30 )
      | ( v3_pre_topc @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('43',plain,
    ( ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 )
        | ( ( k1_tops_1 @ X31 @ X30 )
         != X30 )
        | ( v3_pre_topc @ X30 @ X31 ) )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 )
        | ( ( k1_tops_1 @ X31 @ X30 )
         != X30 )
        | ( v3_pre_topc @ X30 @ X31 ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) )
   <= ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 )
        | ( ( k1_tops_1 @ X31 @ X30 )
         != X30 )
        | ( v3_pre_topc @ X30 @ X31 ) )
    | ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('50',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( ( k1_tops_1 @ X31 @ X30 )
       != X30 )
      | ( v3_pre_topc @ X30 @ X31 ) ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( ( k1_tops_1 @ X31 @ X30 )
       != X30 )
      | ( v3_pre_topc @ X30 @ X31 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k1_tops_1 @ X33 @ X32 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X33 ) @ X32 @ ( k2_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('64',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['63','70'])).

thf('72',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('73',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf('76',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','74','75'])).

thf('77',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('78',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['76','87'])).

thf('89',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('91',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['91'])).

thf('93',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['91'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['91'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('100',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('101',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('103',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('106',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','38','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['104','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k2_tops_1 @ sk_A @ sk_B )
        = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','107'])).

thf('109',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','108'])).

thf('110',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('113',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['91'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('117',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('118',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('124',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('127',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['125','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['116','129'])).

thf('131',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['132','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('139',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1
        = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('146',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['144','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['115','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['110','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('154',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['125','128'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['116','129'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X2 )
      | ( X2
        = ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('162',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('163',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['161','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['160','165'])).

thf('167',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
      = X0 ) ),
    inference(demod,[status(thm)],['152','153','170'])).

thf('172',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simplify,[status(thm)],['109'])).

thf('173',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('174',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','169'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('178',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','74','75'])).

thf('179',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['174','175','176','177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['171','179'])).

thf('181',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['90','180'])).

thf('182',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['55','181'])).

thf('183',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    $false ),
    inference(demod,[status(thm)],['40','183'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zUBqN1QsRU
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.90/2.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.90/2.11  % Solved by: fo/fo7.sh
% 1.90/2.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.90/2.11  % done 2834 iterations in 1.649s
% 1.90/2.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.90/2.11  % SZS output start Refutation
% 1.90/2.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.90/2.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.90/2.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.90/2.11  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.90/2.11  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.90/2.11  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.90/2.11  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.90/2.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.90/2.11  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.90/2.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.90/2.11  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.90/2.11  thf(sk_A_type, type, sk_A: $i).
% 1.90/2.11  thf(sk_B_type, type, sk_B: $i).
% 1.90/2.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.90/2.11  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.90/2.11  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.90/2.11  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.90/2.11  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.90/2.11  thf(t76_tops_1, conjecture,
% 1.90/2.11    (![A:$i]:
% 1.90/2.11     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.90/2.11       ( ![B:$i]:
% 1.90/2.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.90/2.11           ( ( v3_pre_topc @ B @ A ) <=>
% 1.90/2.11             ( ( k2_tops_1 @ A @ B ) =
% 1.90/2.11               ( k7_subset_1 @
% 1.90/2.11                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 1.90/2.11  thf(zf_stmt_0, negated_conjecture,
% 1.90/2.11    (~( ![A:$i]:
% 1.90/2.11        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.90/2.11          ( ![B:$i]:
% 1.90/2.11            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.90/2.11              ( ( v3_pre_topc @ B @ A ) <=>
% 1.90/2.11                ( ( k2_tops_1 @ A @ B ) =
% 1.90/2.11                  ( k7_subset_1 @
% 1.90/2.11                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 1.90/2.11    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 1.90/2.11  thf('0', plain,
% 1.90/2.11      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.90/2.11        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('1', plain,
% 1.90/2.11      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.90/2.11      inference('split', [status(esa)], ['0'])).
% 1.90/2.11  thf('2', plain,
% 1.90/2.11      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 1.90/2.11       ~
% 1.90/2.11       (((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 1.90/2.11      inference('split', [status(esa)], ['0'])).
% 1.90/2.11  thf('3', plain,
% 1.90/2.11      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.90/2.11        | (v3_pre_topc @ sk_B @ sk_A))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('4', plain,
% 1.90/2.11      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.90/2.11      inference('split', [status(esa)], ['3'])).
% 1.90/2.11  thf('5', plain,
% 1.90/2.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf(t55_tops_1, axiom,
% 1.90/2.11    (![A:$i]:
% 1.90/2.11     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.90/2.11       ( ![B:$i]:
% 1.90/2.11         ( ( l1_pre_topc @ B ) =>
% 1.90/2.11           ( ![C:$i]:
% 1.90/2.11             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.90/2.11               ( ![D:$i]:
% 1.90/2.11                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.90/2.11                   ( ( ( v3_pre_topc @ D @ B ) =>
% 1.90/2.11                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 1.90/2.11                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 1.90/2.11                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 1.90/2.11  thf('6', plain,
% 1.90/2.11      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.90/2.11         (~ (l1_pre_topc @ X28)
% 1.90/2.11          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.90/2.11          | ~ (v3_pre_topc @ X29 @ X28)
% 1.90/2.11          | ((k1_tops_1 @ X28 @ X29) = (X29))
% 1.90/2.11          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.90/2.11          | ~ (l1_pre_topc @ X31)
% 1.90/2.11          | ~ (v2_pre_topc @ X31))),
% 1.90/2.11      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.90/2.11  thf('7', plain,
% 1.90/2.11      ((![X28 : $i, X29 : $i]:
% 1.90/2.11          (~ (l1_pre_topc @ X28)
% 1.90/2.11           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.90/2.11           | ~ (v3_pre_topc @ X29 @ X28)
% 1.90/2.11           | ((k1_tops_1 @ X28 @ X29) = (X29))))
% 1.90/2.11         <= ((![X28 : $i, X29 : $i]:
% 1.90/2.11                (~ (l1_pre_topc @ X28)
% 1.90/2.11                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.90/2.11                 | ~ (v3_pre_topc @ X29 @ X28)
% 1.90/2.11                 | ((k1_tops_1 @ X28 @ X29) = (X29)))))),
% 1.90/2.11      inference('split', [status(esa)], ['6'])).
% 1.90/2.11  thf('8', plain,
% 1.90/2.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('9', plain,
% 1.90/2.11      ((![X30 : $i, X31 : $i]:
% 1.90/2.11          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.90/2.11           | ~ (l1_pre_topc @ X31)
% 1.90/2.11           | ~ (v2_pre_topc @ X31)))
% 1.90/2.11         <= ((![X30 : $i, X31 : $i]:
% 1.90/2.11                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.90/2.11                 | ~ (l1_pre_topc @ X31)
% 1.90/2.11                 | ~ (v2_pre_topc @ X31))))),
% 1.90/2.11      inference('split', [status(esa)], ['6'])).
% 1.90/2.11  thf('10', plain,
% 1.90/2.11      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 1.90/2.11         <= ((![X30 : $i, X31 : $i]:
% 1.90/2.11                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.90/2.11                 | ~ (l1_pre_topc @ X31)
% 1.90/2.11                 | ~ (v2_pre_topc @ X31))))),
% 1.90/2.11      inference('sup-', [status(thm)], ['8', '9'])).
% 1.90/2.11  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('13', plain,
% 1.90/2.11      (~
% 1.90/2.11       (![X30 : $i, X31 : $i]:
% 1.90/2.11          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.90/2.11           | ~ (l1_pre_topc @ X31)
% 1.90/2.11           | ~ (v2_pre_topc @ X31)))),
% 1.90/2.11      inference('demod', [status(thm)], ['10', '11', '12'])).
% 1.90/2.11  thf('14', plain,
% 1.90/2.11      ((![X28 : $i, X29 : $i]:
% 1.90/2.11          (~ (l1_pre_topc @ X28)
% 1.90/2.11           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.90/2.11           | ~ (v3_pre_topc @ X29 @ X28)
% 1.90/2.11           | ((k1_tops_1 @ X28 @ X29) = (X29)))) | 
% 1.90/2.11       (![X30 : $i, X31 : $i]:
% 1.90/2.11          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.90/2.11           | ~ (l1_pre_topc @ X31)
% 1.90/2.11           | ~ (v2_pre_topc @ X31)))),
% 1.90/2.11      inference('split', [status(esa)], ['6'])).
% 1.90/2.11  thf('15', plain,
% 1.90/2.11      ((![X28 : $i, X29 : $i]:
% 1.90/2.11          (~ (l1_pre_topc @ X28)
% 1.90/2.11           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.90/2.11           | ~ (v3_pre_topc @ X29 @ X28)
% 1.90/2.11           | ((k1_tops_1 @ X28 @ X29) = (X29))))),
% 1.90/2.11      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 1.90/2.11  thf('16', plain,
% 1.90/2.11      (![X28 : $i, X29 : $i]:
% 1.90/2.11         (~ (l1_pre_topc @ X28)
% 1.90/2.11          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.90/2.11          | ~ (v3_pre_topc @ X29 @ X28)
% 1.90/2.11          | ((k1_tops_1 @ X28 @ X29) = (X29)))),
% 1.90/2.11      inference('simpl_trail', [status(thm)], ['7', '15'])).
% 1.90/2.11  thf('17', plain,
% 1.90/2.11      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 1.90/2.11        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 1.90/2.11        | ~ (l1_pre_topc @ sk_A))),
% 1.90/2.11      inference('sup-', [status(thm)], ['5', '16'])).
% 1.90/2.11  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('19', plain,
% 1.90/2.11      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.90/2.11      inference('demod', [status(thm)], ['17', '18'])).
% 1.90/2.11  thf('20', plain,
% 1.90/2.11      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.90/2.11         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['4', '19'])).
% 1.90/2.11  thf('21', plain,
% 1.90/2.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf(l78_tops_1, axiom,
% 1.90/2.11    (![A:$i]:
% 1.90/2.11     ( ( l1_pre_topc @ A ) =>
% 1.90/2.11       ( ![B:$i]:
% 1.90/2.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.90/2.11           ( ( k2_tops_1 @ A @ B ) =
% 1.90/2.11             ( k7_subset_1 @
% 1.90/2.11               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.90/2.11               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.90/2.11  thf('22', plain,
% 1.90/2.11      (![X26 : $i, X27 : $i]:
% 1.90/2.11         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.90/2.11          | ((k2_tops_1 @ X27 @ X26)
% 1.90/2.11              = (k7_subset_1 @ (u1_struct_0 @ X27) @ 
% 1.90/2.11                 (k2_pre_topc @ X27 @ X26) @ (k1_tops_1 @ X27 @ X26)))
% 1.90/2.11          | ~ (l1_pre_topc @ X27))),
% 1.90/2.11      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.90/2.11  thf('23', plain,
% 1.90/2.11      ((~ (l1_pre_topc @ sk_A)
% 1.90/2.11        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.90/2.11      inference('sup-', [status(thm)], ['21', '22'])).
% 1.90/2.11  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('25', plain,
% 1.90/2.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf(dt_k2_pre_topc, axiom,
% 1.90/2.11    (![A:$i,B:$i]:
% 1.90/2.11     ( ( ( l1_pre_topc @ A ) & 
% 1.90/2.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.90/2.11       ( m1_subset_1 @
% 1.90/2.11         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.90/2.11  thf('26', plain,
% 1.90/2.11      (![X24 : $i, X25 : $i]:
% 1.90/2.11         (~ (l1_pre_topc @ X24)
% 1.90/2.11          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.90/2.11          | (m1_subset_1 @ (k2_pre_topc @ X24 @ X25) @ 
% 1.90/2.11             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 1.90/2.11      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.90/2.11  thf('27', plain,
% 1.90/2.11      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.90/2.11         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.90/2.11        | ~ (l1_pre_topc @ sk_A))),
% 1.90/2.11      inference('sup-', [status(thm)], ['25', '26'])).
% 1.90/2.11  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('29', plain,
% 1.90/2.11      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.90/2.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.90/2.11      inference('demod', [status(thm)], ['27', '28'])).
% 1.90/2.11  thf(redefinition_k7_subset_1, axiom,
% 1.90/2.11    (![A:$i,B:$i,C:$i]:
% 1.90/2.11     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.90/2.11       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.90/2.11  thf('30', plain,
% 1.90/2.11      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.90/2.11         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 1.90/2.11          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 1.90/2.11      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.90/2.11  thf('31', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.90/2.11           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.90/2.11      inference('sup-', [status(thm)], ['29', '30'])).
% 1.90/2.11  thf('32', plain,
% 1.90/2.11      (((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.90/2.11            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.90/2.11      inference('demod', [status(thm)], ['23', '24', '31'])).
% 1.90/2.11  thf('33', plain,
% 1.90/2.11      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.90/2.11         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.90/2.11      inference('sup+', [status(thm)], ['20', '32'])).
% 1.90/2.11  thf('34', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.90/2.11           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.90/2.11      inference('sup-', [status(thm)], ['29', '30'])).
% 1.90/2.11  thf('35', plain,
% 1.90/2.11      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.90/2.11         <= (~
% 1.90/2.11             (((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.90/2.11      inference('split', [status(esa)], ['0'])).
% 1.90/2.11  thf('36', plain,
% 1.90/2.11      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.90/2.11         <= (~
% 1.90/2.11             (((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.90/2.11      inference('sup-', [status(thm)], ['34', '35'])).
% 1.90/2.11  thf('37', plain,
% 1.90/2.11      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.90/2.11         <= (~
% 1.90/2.11             (((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 1.90/2.11             ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['33', '36'])).
% 1.90/2.11  thf('38', plain,
% 1.90/2.11      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.90/2.11       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.90/2.11      inference('simplify', [status(thm)], ['37'])).
% 1.90/2.11  thf('39', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.90/2.11      inference('sat_resolution*', [status(thm)], ['2', '38'])).
% 1.90/2.11  thf('40', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 1.90/2.11      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 1.90/2.11  thf('41', plain,
% 1.90/2.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('42', plain,
% 1.90/2.11      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.90/2.11         (~ (l1_pre_topc @ X28)
% 1.90/2.11          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.90/2.11          | ((k1_tops_1 @ X31 @ X30) != (X30))
% 1.90/2.11          | (v3_pre_topc @ X30 @ X31)
% 1.90/2.11          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.90/2.11          | ~ (l1_pre_topc @ X31)
% 1.90/2.11          | ~ (v2_pre_topc @ X31))),
% 1.90/2.11      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.90/2.11  thf('43', plain,
% 1.90/2.11      ((![X30 : $i, X31 : $i]:
% 1.90/2.11          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.90/2.11           | ~ (l1_pre_topc @ X31)
% 1.90/2.11           | ~ (v2_pre_topc @ X31)
% 1.90/2.11           | ((k1_tops_1 @ X31 @ X30) != (X30))
% 1.90/2.11           | (v3_pre_topc @ X30 @ X31)))
% 1.90/2.11         <= ((![X30 : $i, X31 : $i]:
% 1.90/2.11                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.90/2.11                 | ~ (l1_pre_topc @ X31)
% 1.90/2.11                 | ~ (v2_pre_topc @ X31)
% 1.90/2.11                 | ((k1_tops_1 @ X31 @ X30) != (X30))
% 1.90/2.11                 | (v3_pre_topc @ X30 @ X31))))),
% 1.90/2.11      inference('split', [status(esa)], ['42'])).
% 1.90/2.11  thf('44', plain,
% 1.90/2.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('45', plain,
% 1.90/2.11      ((![X28 : $i, X29 : $i]:
% 1.90/2.11          (~ (l1_pre_topc @ X28)
% 1.90/2.11           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))))
% 1.90/2.11         <= ((![X28 : $i, X29 : $i]:
% 1.90/2.11                (~ (l1_pre_topc @ X28)
% 1.90/2.11                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28))))))),
% 1.90/2.11      inference('split', [status(esa)], ['42'])).
% 1.90/2.11  thf('46', plain,
% 1.90/2.11      ((~ (l1_pre_topc @ sk_A))
% 1.90/2.11         <= ((![X28 : $i, X29 : $i]:
% 1.90/2.11                (~ (l1_pre_topc @ X28)
% 1.90/2.11                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28))))))),
% 1.90/2.11      inference('sup-', [status(thm)], ['44', '45'])).
% 1.90/2.11  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('48', plain,
% 1.90/2.11      (~
% 1.90/2.11       (![X28 : $i, X29 : $i]:
% 1.90/2.11          (~ (l1_pre_topc @ X28)
% 1.90/2.11           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))))),
% 1.90/2.11      inference('demod', [status(thm)], ['46', '47'])).
% 1.90/2.11  thf('49', plain,
% 1.90/2.11      ((![X30 : $i, X31 : $i]:
% 1.90/2.11          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.90/2.11           | ~ (l1_pre_topc @ X31)
% 1.90/2.11           | ~ (v2_pre_topc @ X31)
% 1.90/2.11           | ((k1_tops_1 @ X31 @ X30) != (X30))
% 1.90/2.11           | (v3_pre_topc @ X30 @ X31))) | 
% 1.90/2.11       (![X28 : $i, X29 : $i]:
% 1.90/2.11          (~ (l1_pre_topc @ X28)
% 1.90/2.11           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))))),
% 1.90/2.11      inference('split', [status(esa)], ['42'])).
% 1.90/2.11  thf('50', plain,
% 1.90/2.11      ((![X30 : $i, X31 : $i]:
% 1.90/2.11          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.90/2.11           | ~ (l1_pre_topc @ X31)
% 1.90/2.11           | ~ (v2_pre_topc @ X31)
% 1.90/2.11           | ((k1_tops_1 @ X31 @ X30) != (X30))
% 1.90/2.11           | (v3_pre_topc @ X30 @ X31)))),
% 1.90/2.11      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 1.90/2.11  thf('51', plain,
% 1.90/2.11      (![X30 : $i, X31 : $i]:
% 1.90/2.11         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.90/2.11          | ~ (l1_pre_topc @ X31)
% 1.90/2.11          | ~ (v2_pre_topc @ X31)
% 1.90/2.11          | ((k1_tops_1 @ X31 @ X30) != (X30))
% 1.90/2.11          | (v3_pre_topc @ X30 @ X31))),
% 1.90/2.11      inference('simpl_trail', [status(thm)], ['43', '50'])).
% 1.90/2.11  thf('52', plain,
% 1.90/2.11      (((v3_pre_topc @ sk_B @ sk_A)
% 1.90/2.11        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 1.90/2.11        | ~ (v2_pre_topc @ sk_A)
% 1.90/2.11        | ~ (l1_pre_topc @ sk_A))),
% 1.90/2.11      inference('sup-', [status(thm)], ['41', '51'])).
% 1.90/2.11  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('55', plain,
% 1.90/2.11      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 1.90/2.11      inference('demod', [status(thm)], ['52', '53', '54'])).
% 1.90/2.11  thf('56', plain,
% 1.90/2.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf(t74_tops_1, axiom,
% 1.90/2.11    (![A:$i]:
% 1.90/2.11     ( ( l1_pre_topc @ A ) =>
% 1.90/2.11       ( ![B:$i]:
% 1.90/2.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.90/2.11           ( ( k1_tops_1 @ A @ B ) =
% 1.90/2.11             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.90/2.11  thf('57', plain,
% 1.90/2.11      (![X32 : $i, X33 : $i]:
% 1.90/2.11         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.90/2.11          | ((k1_tops_1 @ X33 @ X32)
% 1.90/2.11              = (k7_subset_1 @ (u1_struct_0 @ X33) @ X32 @ 
% 1.90/2.11                 (k2_tops_1 @ X33 @ X32)))
% 1.90/2.11          | ~ (l1_pre_topc @ X33))),
% 1.90/2.11      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.90/2.11  thf('58', plain,
% 1.90/2.11      ((~ (l1_pre_topc @ sk_A)
% 1.90/2.11        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.90/2.11            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.90/2.11               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.90/2.11      inference('sup-', [status(thm)], ['56', '57'])).
% 1.90/2.11  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('60', plain,
% 1.90/2.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('61', plain,
% 1.90/2.11      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.90/2.11         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 1.90/2.11          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 1.90/2.11      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.90/2.11  thf('62', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.90/2.11           = (k4_xboole_0 @ sk_B @ X0))),
% 1.90/2.11      inference('sup-', [status(thm)], ['60', '61'])).
% 1.90/2.11  thf('63', plain,
% 1.90/2.11      (((k1_tops_1 @ sk_A @ sk_B)
% 1.90/2.11         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.90/2.11      inference('demod', [status(thm)], ['58', '59', '62'])).
% 1.90/2.11  thf(t36_xboole_1, axiom,
% 1.90/2.11    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.90/2.11  thf('64', plain,
% 1.90/2.11      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 1.90/2.11      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.90/2.11  thf(t28_xboole_1, axiom,
% 1.90/2.11    (![A:$i,B:$i]:
% 1.90/2.11     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.90/2.11  thf('65', plain,
% 1.90/2.11      (![X13 : $i, X14 : $i]:
% 1.90/2.11         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.90/2.11      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.90/2.11  thf('66', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.90/2.11           = (k4_xboole_0 @ X0 @ X1))),
% 1.90/2.11      inference('sup-', [status(thm)], ['64', '65'])).
% 1.90/2.11  thf(commutativity_k3_xboole_0, axiom,
% 1.90/2.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.90/2.11  thf('67', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.90/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.90/2.11  thf('68', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.90/2.11           = (k4_xboole_0 @ X0 @ X1))),
% 1.90/2.11      inference('demod', [status(thm)], ['66', '67'])).
% 1.90/2.11  thf(t100_xboole_1, axiom,
% 1.90/2.11    (![A:$i,B:$i]:
% 1.90/2.11     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.90/2.11  thf('69', plain,
% 1.90/2.11      (![X11 : $i, X12 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X11 @ X12)
% 1.90/2.11           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.90/2.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.90/2.11  thf('70', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.90/2.11           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.90/2.11      inference('sup+', [status(thm)], ['68', '69'])).
% 1.90/2.11  thf('71', plain,
% 1.90/2.11      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.90/2.11         = (k5_xboole_0 @ sk_B @ 
% 1.90/2.11            (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.90/2.11      inference('sup+', [status(thm)], ['63', '70'])).
% 1.90/2.11  thf('72', plain,
% 1.90/2.11      (((k1_tops_1 @ sk_A @ sk_B)
% 1.90/2.11         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.90/2.11      inference('demod', [status(thm)], ['58', '59', '62'])).
% 1.90/2.11  thf(t48_xboole_1, axiom,
% 1.90/2.11    (![A:$i,B:$i]:
% 1.90/2.11     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.90/2.11  thf('73', plain,
% 1.90/2.11      (![X17 : $i, X18 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.90/2.11           = (k3_xboole_0 @ X17 @ X18))),
% 1.90/2.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.90/2.11  thf('74', plain,
% 1.90/2.11      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.90/2.11         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.90/2.11      inference('sup+', [status(thm)], ['72', '73'])).
% 1.90/2.11  thf('75', plain,
% 1.90/2.11      (((k1_tops_1 @ sk_A @ sk_B)
% 1.90/2.11         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.90/2.11      inference('demod', [status(thm)], ['58', '59', '62'])).
% 1.90/2.11  thf('76', plain,
% 1.90/2.11      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.90/2.11         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.90/2.11      inference('demod', [status(thm)], ['71', '74', '75'])).
% 1.90/2.11  thf('77', plain,
% 1.90/2.11      (![X17 : $i, X18 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.90/2.11           = (k3_xboole_0 @ X17 @ X18))),
% 1.90/2.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.90/2.11  thf('78', plain,
% 1.90/2.11      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 1.90/2.11      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.90/2.11  thf('79', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.90/2.11      inference('sup+', [status(thm)], ['77', '78'])).
% 1.90/2.11  thf('80', plain,
% 1.90/2.11      (![X13 : $i, X14 : $i]:
% 1.90/2.11         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.90/2.11      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.90/2.11  thf('81', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.90/2.11           = (k3_xboole_0 @ X0 @ X1))),
% 1.90/2.11      inference('sup-', [status(thm)], ['79', '80'])).
% 1.90/2.11  thf('82', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.90/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.90/2.11  thf('83', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.90/2.11           = (k3_xboole_0 @ X0 @ X1))),
% 1.90/2.11      inference('demod', [status(thm)], ['81', '82'])).
% 1.90/2.11  thf('84', plain,
% 1.90/2.11      (![X11 : $i, X12 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X11 @ X12)
% 1.90/2.11           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.90/2.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.90/2.11  thf('85', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.90/2.11           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.90/2.11      inference('sup+', [status(thm)], ['83', '84'])).
% 1.90/2.11  thf('86', plain,
% 1.90/2.11      (![X11 : $i, X12 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X11 @ X12)
% 1.90/2.11           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.90/2.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.90/2.11  thf('87', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.90/2.11           = (k4_xboole_0 @ X1 @ X0))),
% 1.90/2.11      inference('demod', [status(thm)], ['85', '86'])).
% 1.90/2.11  thf('88', plain,
% 1.90/2.11      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.90/2.11         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.90/2.11      inference('sup+', [status(thm)], ['76', '87'])).
% 1.90/2.11  thf('89', plain,
% 1.90/2.11      (((k1_tops_1 @ sk_A @ sk_B)
% 1.90/2.11         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.90/2.11      inference('demod', [status(thm)], ['58', '59', '62'])).
% 1.90/2.11  thf('90', plain,
% 1.90/2.11      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.90/2.11         = (k1_tops_1 @ sk_A @ sk_B))),
% 1.90/2.11      inference('demod', [status(thm)], ['88', '89'])).
% 1.90/2.11  thf(d5_xboole_0, axiom,
% 1.90/2.11    (![A:$i,B:$i,C:$i]:
% 1.90/2.11     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.90/2.11       ( ![D:$i]:
% 1.90/2.11         ( ( r2_hidden @ D @ C ) <=>
% 1.90/2.11           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.90/2.11  thf('91', plain,
% 1.90/2.11      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.90/2.11         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.90/2.11          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.90/2.11          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.90/2.11      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.90/2.11  thf('92', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.90/2.11          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.90/2.11      inference('eq_fact', [status(thm)], ['91'])).
% 1.90/2.11  thf('93', plain,
% 1.90/2.11      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.90/2.11         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.90/2.11          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.90/2.11          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.90/2.11          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.90/2.11      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.90/2.11  thf('94', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.90/2.11          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.90/2.11          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.90/2.11          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['92', '93'])).
% 1.90/2.11  thf('95', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.90/2.11          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.90/2.11          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.90/2.11      inference('simplify', [status(thm)], ['94'])).
% 1.90/2.11  thf('96', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.90/2.11          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.90/2.11      inference('eq_fact', [status(thm)], ['91'])).
% 1.90/2.11  thf('97', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.90/2.11          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.90/2.11      inference('clc', [status(thm)], ['95', '96'])).
% 1.90/2.11  thf('98', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.90/2.11          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.90/2.11      inference('eq_fact', [status(thm)], ['91'])).
% 1.90/2.11  thf('99', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.90/2.11           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.90/2.11      inference('sup-', [status(thm)], ['29', '30'])).
% 1.90/2.11  thf('100', plain,
% 1.90/2.11      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.90/2.11         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.90/2.11      inference('split', [status(esa)], ['3'])).
% 1.90/2.11  thf('101', plain,
% 1.90/2.11      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.90/2.11         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.90/2.11      inference('sup+', [status(thm)], ['99', '100'])).
% 1.90/2.11  thf('102', plain,
% 1.90/2.11      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.90/2.11         (~ (r2_hidden @ X6 @ X5)
% 1.90/2.11          | ~ (r2_hidden @ X6 @ X4)
% 1.90/2.11          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.90/2.11      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.90/2.11  thf('103', plain,
% 1.90/2.11      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.90/2.11         (~ (r2_hidden @ X6 @ X4)
% 1.90/2.11          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.90/2.11      inference('simplify', [status(thm)], ['102'])).
% 1.90/2.11  thf('104', plain,
% 1.90/2.11      ((![X0 : $i]:
% 1.90/2.11          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 1.90/2.11           | ~ (r2_hidden @ X0 @ sk_B)))
% 1.90/2.11         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.90/2.11      inference('sup-', [status(thm)], ['101', '103'])).
% 1.90/2.11  thf('105', plain,
% 1.90/2.11      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.90/2.11       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.90/2.11      inference('split', [status(esa)], ['3'])).
% 1.90/2.11  thf('106', plain,
% 1.90/2.11      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.90/2.11             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 1.90/2.11      inference('sat_resolution*', [status(thm)], ['2', '38', '105'])).
% 1.90/2.11  thf('107', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 1.90/2.11          | ~ (r2_hidden @ X0 @ sk_B))),
% 1.90/2.11      inference('simpl_trail', [status(thm)], ['104', '106'])).
% 1.90/2.11  thf('108', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         (((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11            = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 1.90/2.11          | ~ (r2_hidden @ 
% 1.90/2.11               (sk_D @ (k2_tops_1 @ sk_A @ sk_B) @ X0 @ 
% 1.90/2.11                (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.90/2.11               sk_B))),
% 1.90/2.11      inference('sup-', [status(thm)], ['98', '107'])).
% 1.90/2.11  thf('109', plain,
% 1.90/2.11      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11          = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.90/2.11        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11            = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['97', '108'])).
% 1.90/2.11  thf('110', plain,
% 1.90/2.11      (((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11         = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.90/2.11      inference('simplify', [status(thm)], ['109'])).
% 1.90/2.11  thf('111', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.90/2.11           = (k4_xboole_0 @ X0 @ X1))),
% 1.90/2.11      inference('demod', [status(thm)], ['66', '67'])).
% 1.90/2.11  thf('112', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.90/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.90/2.11  thf('113', plain,
% 1.90/2.11      (![X11 : $i, X12 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X11 @ X12)
% 1.90/2.11           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.90/2.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.90/2.11  thf('114', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X0 @ X1)
% 1.90/2.11           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.90/2.11      inference('sup+', [status(thm)], ['112', '113'])).
% 1.90/2.11  thf('115', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 1.90/2.11           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.90/2.11      inference('sup+', [status(thm)], ['111', '114'])).
% 1.90/2.11  thf('116', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.90/2.11          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.90/2.11      inference('eq_fact', [status(thm)], ['91'])).
% 1.90/2.11  thf(d10_xboole_0, axiom,
% 1.90/2.11    (![A:$i,B:$i]:
% 1.90/2.11     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.90/2.11  thf('117', plain,
% 1.90/2.11      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 1.90/2.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.90/2.11  thf('118', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.90/2.11      inference('simplify', [status(thm)], ['117'])).
% 1.90/2.11  thf('119', plain,
% 1.90/2.11      (![X13 : $i, X14 : $i]:
% 1.90/2.11         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.90/2.11      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.90/2.11  thf('120', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.90/2.11      inference('sup-', [status(thm)], ['118', '119'])).
% 1.90/2.11  thf('121', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X0 @ X1)
% 1.90/2.11           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.90/2.11      inference('sup+', [status(thm)], ['112', '113'])).
% 1.90/2.11  thf('122', plain,
% 1.90/2.11      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.90/2.11      inference('sup+', [status(thm)], ['120', '121'])).
% 1.90/2.11  thf('123', plain,
% 1.90/2.11      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.90/2.11         (~ (r2_hidden @ X6 @ X5)
% 1.90/2.11          | (r2_hidden @ X6 @ X3)
% 1.90/2.11          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.90/2.11      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.90/2.11  thf('124', plain,
% 1.90/2.11      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.90/2.11         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.90/2.11      inference('simplify', [status(thm)], ['123'])).
% 1.90/2.11  thf('125', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 1.90/2.11      inference('sup-', [status(thm)], ['122', '124'])).
% 1.90/2.11  thf('126', plain,
% 1.90/2.11      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.90/2.11      inference('sup+', [status(thm)], ['120', '121'])).
% 1.90/2.11  thf('127', plain,
% 1.90/2.11      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.90/2.11         (~ (r2_hidden @ X6 @ X4)
% 1.90/2.11          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.90/2.11      inference('simplify', [status(thm)], ['102'])).
% 1.90/2.11  thf('128', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 1.90/2.11          | ~ (r2_hidden @ X1 @ X0))),
% 1.90/2.11      inference('sup-', [status(thm)], ['126', '127'])).
% 1.90/2.11  thf('129', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 1.90/2.11      inference('clc', [status(thm)], ['125', '128'])).
% 1.90/2.11  thf('130', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k5_xboole_0 @ X0 @ X0)
% 1.90/2.11           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 1.90/2.11      inference('sup-', [status(thm)], ['116', '129'])).
% 1.90/2.11  thf('131', plain,
% 1.90/2.11      (![X17 : $i, X18 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.90/2.11           = (k3_xboole_0 @ X17 @ X18))),
% 1.90/2.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.90/2.11  thf('132', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k5_xboole_0 @ X0 @ X0)
% 1.90/2.11           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 1.90/2.11      inference('sup+', [status(thm)], ['130', '131'])).
% 1.90/2.11  thf('133', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.90/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.90/2.11  thf('134', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.90/2.11      inference('sup+', [status(thm)], ['77', '78'])).
% 1.90/2.11  thf('135', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.90/2.11      inference('sup+', [status(thm)], ['133', '134'])).
% 1.90/2.11  thf('136', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 1.90/2.11      inference('sup+', [status(thm)], ['132', '135'])).
% 1.90/2.11  thf('137', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k5_xboole_0 @ X0 @ X0)
% 1.90/2.11           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 1.90/2.11      inference('sup+', [status(thm)], ['130', '131'])).
% 1.90/2.11  thf('138', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.90/2.11      inference('sup+', [status(thm)], ['133', '134'])).
% 1.90/2.11  thf('139', plain,
% 1.90/2.11      (![X8 : $i, X10 : $i]:
% 1.90/2.11         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.90/2.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.90/2.11  thf('140', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.90/2.11          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['138', '139'])).
% 1.90/2.11  thf('141', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 1.90/2.11          | ((X1) = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['137', '140'])).
% 1.90/2.11  thf('142', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k5_xboole_0 @ X0 @ X0)
% 1.90/2.11           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 1.90/2.11      inference('sup+', [status(thm)], ['130', '131'])).
% 1.90/2.11  thf('143', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 1.90/2.11          | ((X1) = (k5_xboole_0 @ X0 @ X0)))),
% 1.90/2.11      inference('demod', [status(thm)], ['141', '142'])).
% 1.90/2.11  thf('144', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X1) = (k5_xboole_0 @ X0 @ X0))),
% 1.90/2.11      inference('sup-', [status(thm)], ['136', '143'])).
% 1.90/2.11  thf('145', plain,
% 1.90/2.11      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.90/2.11      inference('sup+', [status(thm)], ['120', '121'])).
% 1.90/2.11  thf('146', plain,
% 1.90/2.11      (![X17 : $i, X18 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.90/2.11           = (k3_xboole_0 @ X17 @ X18))),
% 1.90/2.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.90/2.11  thf('147', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 1.90/2.11           = (k3_xboole_0 @ X0 @ X0))),
% 1.90/2.11      inference('sup+', [status(thm)], ['145', '146'])).
% 1.90/2.11  thf('148', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.90/2.11      inference('sup-', [status(thm)], ['118', '119'])).
% 1.90/2.11  thf('149', plain,
% 1.90/2.11      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 1.90/2.11      inference('demod', [status(thm)], ['147', '148'])).
% 1.90/2.11  thf('150', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 1.90/2.11      inference('sup+', [status(thm)], ['144', '149'])).
% 1.90/2.11  thf('151', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 1.90/2.11           = (X2))),
% 1.90/2.11      inference('sup+', [status(thm)], ['115', '150'])).
% 1.90/2.11  thf('152', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X0 @ 
% 1.90/2.11           (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.90/2.11           = (X0))),
% 1.90/2.11      inference('sup+', [status(thm)], ['110', '151'])).
% 1.90/2.11  thf('153', plain,
% 1.90/2.11      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.90/2.11      inference('sup+', [status(thm)], ['120', '121'])).
% 1.90/2.11  thf('154', plain,
% 1.90/2.11      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.90/2.11         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.90/2.11          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.90/2.11          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.90/2.11      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.90/2.11  thf('155', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 1.90/2.11      inference('clc', [status(thm)], ['125', '128'])).
% 1.90/2.11  thf('156', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.11         ((r2_hidden @ (sk_D @ X2 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ X2)
% 1.90/2.11          | ((X2) = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['154', '155'])).
% 1.90/2.11  thf('157', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k5_xboole_0 @ X0 @ X0)
% 1.90/2.11           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 1.90/2.11      inference('sup-', [status(thm)], ['116', '129'])).
% 1.90/2.11  thf('158', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.11         ((r2_hidden @ (sk_D @ X2 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ X2)
% 1.90/2.11          | ((X2) = (k5_xboole_0 @ X0 @ X0)))),
% 1.90/2.11      inference('demod', [status(thm)], ['156', '157'])).
% 1.90/2.11  thf('159', plain,
% 1.90/2.11      (((k1_tops_1 @ sk_A @ sk_B)
% 1.90/2.11         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.90/2.11      inference('demod', [status(thm)], ['58', '59', '62'])).
% 1.90/2.11  thf('160', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]:
% 1.90/2.11         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.90/2.11           = (k4_xboole_0 @ X0 @ X1))),
% 1.90/2.11      inference('demod', [status(thm)], ['66', '67'])).
% 1.90/2.11  thf('161', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.90/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.90/2.11  thf('162', plain,
% 1.90/2.11      (![X17 : $i, X18 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.90/2.11           = (k3_xboole_0 @ X17 @ X18))),
% 1.90/2.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.90/2.11  thf('163', plain,
% 1.90/2.11      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.90/2.11         (~ (r2_hidden @ X6 @ X4)
% 1.90/2.11          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.90/2.11      inference('simplify', [status(thm)], ['102'])).
% 1.90/2.11  thf('164', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.11         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.90/2.11          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['162', '163'])).
% 1.90/2.11  thf('165', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.11         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.90/2.11          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['161', '164'])).
% 1.90/2.11  thf('166', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.11         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 1.90/2.11          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['160', '165'])).
% 1.90/2.11  thf('167', plain,
% 1.90/2.11      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.90/2.11         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.90/2.11      inference('simplify', [status(thm)], ['123'])).
% 1.90/2.11  thf('168', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.11         ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 1.90/2.11      inference('clc', [status(thm)], ['166', '167'])).
% 1.90/2.11  thf('169', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.90/2.11      inference('sup-', [status(thm)], ['159', '168'])).
% 1.90/2.11  thf('170', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.90/2.11           = (k5_xboole_0 @ X0 @ X0))),
% 1.90/2.11      inference('sup-', [status(thm)], ['158', '169'])).
% 1.90/2.11  thf('171', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.90/2.11           = (X0))),
% 1.90/2.11      inference('demod', [status(thm)], ['152', '153', '170'])).
% 1.90/2.11  thf('172', plain,
% 1.90/2.11      (((k2_tops_1 @ sk_A @ sk_B)
% 1.90/2.11         = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.90/2.11      inference('simplify', [status(thm)], ['109'])).
% 1.90/2.11  thf('173', plain,
% 1.90/2.11      (![X17 : $i, X18 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.90/2.11           = (k3_xboole_0 @ X17 @ X18))),
% 1.90/2.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.90/2.11  thf('174', plain,
% 1.90/2.11      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.90/2.11         = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.90/2.11      inference('sup+', [status(thm)], ['172', '173'])).
% 1.90/2.11  thf('175', plain,
% 1.90/2.11      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.90/2.11      inference('sup+', [status(thm)], ['120', '121'])).
% 1.90/2.11  thf('176', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.90/2.11           = (k5_xboole_0 @ X0 @ X0))),
% 1.90/2.11      inference('sup-', [status(thm)], ['158', '169'])).
% 1.90/2.11  thf('177', plain,
% 1.90/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.90/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.90/2.11  thf('178', plain,
% 1.90/2.11      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.90/2.11         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.90/2.11      inference('demod', [status(thm)], ['71', '74', '75'])).
% 1.90/2.11  thf('179', plain,
% 1.90/2.11      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.90/2.11         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.90/2.11      inference('demod', [status(thm)], ['174', '175', '176', '177', '178'])).
% 1.90/2.11  thf('180', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.90/2.11           = (X0))),
% 1.90/2.11      inference('demod', [status(thm)], ['171', '179'])).
% 1.90/2.11  thf('181', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 1.90/2.11      inference('demod', [status(thm)], ['90', '180'])).
% 1.90/2.11  thf('182', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 1.90/2.11      inference('demod', [status(thm)], ['55', '181'])).
% 1.90/2.11  thf('183', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 1.90/2.11      inference('simplify', [status(thm)], ['182'])).
% 1.90/2.11  thf('184', plain, ($false), inference('demod', [status(thm)], ['40', '183'])).
% 1.90/2.11  
% 1.90/2.11  % SZS output end Refutation
% 1.90/2.11  
% 1.90/2.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
