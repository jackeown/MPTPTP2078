%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZcTHrz7L3f

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:30 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 660 expanded)
%              Number of leaves         :   31 ( 203 expanded)
%              Depth                    :   23
%              Number of atoms          : 1638 (7593 expanded)
%              Number of equality atoms :  117 ( 540 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X33 @ X32 )
      | ( ( k1_tops_1 @ X32 @ X33 )
        = X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('7',plain,
    ( ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( v3_pre_topc @ X33 @ X32 )
        | ( ( k1_tops_1 @ X32 @ X33 )
          = X33 ) )
   <= ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( v3_pre_topc @ X33 @ X32 )
        | ( ( k1_tops_1 @ X32 @ X33 )
          = X33 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) )
   <= ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( v3_pre_topc @ X33 @ X32 )
        | ( ( k1_tops_1 @ X32 @ X33 )
          = X33 ) )
    | ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X33 @ X32 )
      | ( ( k1_tops_1 @ X32 @ X33 )
        = X33 ) ) ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X33 @ X32 )
      | ( ( k1_tops_1 @ X32 @ X33 )
        = X33 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k2_tops_1 @ X31 @ X30 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_pre_topc @ X31 @ X30 ) @ ( k1_tops_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k1_tops_1 @ X35 @ X34 )
       != X34 )
      | ( v3_pre_topc @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('43',plain,
    ( ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 )
        | ( ( k1_tops_1 @ X35 @ X34 )
         != X34 )
        | ( v3_pre_topc @ X34 @ X35 ) )
   <= ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 )
        | ( ( k1_tops_1 @ X35 @ X34 )
         != X34 )
        | ( v3_pre_topc @ X34 @ X35 ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) )
   <= ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 )
        | ( ( k1_tops_1 @ X35 @ X34 )
         != X34 )
        | ( v3_pre_topc @ X34 @ X35 ) )
    | ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('50',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( ( k1_tops_1 @ X35 @ X34 )
       != X34 )
      | ( v3_pre_topc @ X34 @ X35 ) ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( ( k1_tops_1 @ X35 @ X34 )
       != X34 )
      | ( v3_pre_topc @ X34 @ X35 ) ) ),
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

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('56',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( X14 != X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['57'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('61',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

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
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('73',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('74',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('78',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('79',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['76','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k5_xboole_0 @ X0 @ X0 ) @ X2 @ X1 ) @ X1 )
      | ( ( k5_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['56','81'])).

thf('83',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['76','80'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k5_xboole_0 @ X0 @ X0 ) @ X2 @ X1 ) @ X2 )
      | ( ( k5_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('87',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('88',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('92',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','38','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['90','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k5_xboole_0 @ X1 @ X1 ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ( ( k5_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['82','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('97',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k1_tops_1 @ X37 @ X36 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 @ ( k2_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99','102'])).

thf('104',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('105',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ( ( k5_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['95','105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('110',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('111',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99','102'])).

thf('113',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['108','113'])).

thf('115',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['76','80'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','69','70'])).

thf('124',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('127',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['125','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['122','131'])).

thf('133',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['114','132'])).

thf('134',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['55','133'])).

thf('135',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    $false ),
    inference(demod,[status(thm)],['40','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZcTHrz7L3f
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.81/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.81/1.03  % Solved by: fo/fo7.sh
% 0.81/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.03  % done 571 iterations in 0.576s
% 0.81/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.81/1.03  % SZS output start Refutation
% 0.81/1.03  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.81/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.81/1.03  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.81/1.03  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.81/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.81/1.03  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.81/1.03  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.81/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.81/1.03  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.81/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.81/1.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.81/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.81/1.03  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.81/1.03  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.81/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.81/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.81/1.03  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.81/1.03  thf(t76_tops_1, conjecture,
% 0.81/1.03    (![A:$i]:
% 0.81/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.81/1.03       ( ![B:$i]:
% 0.81/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.03           ( ( v3_pre_topc @ B @ A ) <=>
% 0.81/1.03             ( ( k2_tops_1 @ A @ B ) =
% 0.81/1.03               ( k7_subset_1 @
% 0.81/1.03                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.81/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.81/1.03    (~( ![A:$i]:
% 0.81/1.03        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.81/1.03          ( ![B:$i]:
% 0.81/1.03            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.03              ( ( v3_pre_topc @ B @ A ) <=>
% 0.81/1.03                ( ( k2_tops_1 @ A @ B ) =
% 0.81/1.03                  ( k7_subset_1 @
% 0.81/1.03                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.81/1.03    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.81/1.03  thf('0', plain,
% 0.81/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.81/1.03        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('1', plain,
% 0.81/1.03      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.81/1.03      inference('split', [status(esa)], ['0'])).
% 0.81/1.03  thf('2', plain,
% 0.81/1.03      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.81/1.03       ~
% 0.81/1.03       (((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.81/1.03      inference('split', [status(esa)], ['0'])).
% 0.81/1.03  thf('3', plain,
% 0.81/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.81/1.03        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('4', plain,
% 0.81/1.03      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.81/1.03      inference('split', [status(esa)], ['3'])).
% 0.81/1.03  thf('5', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf(t55_tops_1, axiom,
% 0.81/1.03    (![A:$i]:
% 0.81/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.81/1.03       ( ![B:$i]:
% 0.81/1.03         ( ( l1_pre_topc @ B ) =>
% 0.81/1.03           ( ![C:$i]:
% 0.81/1.03             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.03               ( ![D:$i]:
% 0.81/1.03                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.81/1.03                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.81/1.03                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.81/1.03                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.81/1.03                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.81/1.03  thf('6', plain,
% 0.81/1.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.81/1.03         (~ (l1_pre_topc @ X32)
% 0.81/1.03          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.81/1.03          | ~ (v3_pre_topc @ X33 @ X32)
% 0.81/1.03          | ((k1_tops_1 @ X32 @ X33) = (X33))
% 0.81/1.03          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.81/1.03          | ~ (l1_pre_topc @ X35)
% 0.81/1.03          | ~ (v2_pre_topc @ X35))),
% 0.81/1.03      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.81/1.03  thf('7', plain,
% 0.81/1.03      ((![X32 : $i, X33 : $i]:
% 0.81/1.03          (~ (l1_pre_topc @ X32)
% 0.81/1.03           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.81/1.03           | ~ (v3_pre_topc @ X33 @ X32)
% 0.81/1.03           | ((k1_tops_1 @ X32 @ X33) = (X33))))
% 0.81/1.03         <= ((![X32 : $i, X33 : $i]:
% 0.81/1.03                (~ (l1_pre_topc @ X32)
% 0.81/1.03                 | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.81/1.03                 | ~ (v3_pre_topc @ X33 @ X32)
% 0.81/1.03                 | ((k1_tops_1 @ X32 @ X33) = (X33)))))),
% 0.81/1.03      inference('split', [status(esa)], ['6'])).
% 0.81/1.03  thf('8', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('9', plain,
% 0.81/1.03      ((![X34 : $i, X35 : $i]:
% 0.81/1.03          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.81/1.03           | ~ (l1_pre_topc @ X35)
% 0.81/1.03           | ~ (v2_pre_topc @ X35)))
% 0.81/1.03         <= ((![X34 : $i, X35 : $i]:
% 0.81/1.03                (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.81/1.03                 | ~ (l1_pre_topc @ X35)
% 0.81/1.03                 | ~ (v2_pre_topc @ X35))))),
% 0.81/1.03      inference('split', [status(esa)], ['6'])).
% 0.81/1.03  thf('10', plain,
% 0.81/1.03      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.81/1.03         <= ((![X34 : $i, X35 : $i]:
% 0.81/1.03                (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.81/1.03                 | ~ (l1_pre_topc @ X35)
% 0.81/1.03                 | ~ (v2_pre_topc @ X35))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['8', '9'])).
% 0.81/1.03  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('13', plain,
% 0.81/1.03      (~
% 0.81/1.03       (![X34 : $i, X35 : $i]:
% 0.81/1.03          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.81/1.03           | ~ (l1_pre_topc @ X35)
% 0.81/1.03           | ~ (v2_pre_topc @ X35)))),
% 0.81/1.03      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.81/1.03  thf('14', plain,
% 0.81/1.03      ((![X32 : $i, X33 : $i]:
% 0.81/1.03          (~ (l1_pre_topc @ X32)
% 0.81/1.03           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.81/1.03           | ~ (v3_pre_topc @ X33 @ X32)
% 0.81/1.03           | ((k1_tops_1 @ X32 @ X33) = (X33)))) | 
% 0.81/1.03       (![X34 : $i, X35 : $i]:
% 0.81/1.03          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.81/1.03           | ~ (l1_pre_topc @ X35)
% 0.81/1.03           | ~ (v2_pre_topc @ X35)))),
% 0.81/1.03      inference('split', [status(esa)], ['6'])).
% 0.81/1.03  thf('15', plain,
% 0.81/1.03      ((![X32 : $i, X33 : $i]:
% 0.81/1.03          (~ (l1_pre_topc @ X32)
% 0.81/1.03           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.81/1.03           | ~ (v3_pre_topc @ X33 @ X32)
% 0.81/1.03           | ((k1_tops_1 @ X32 @ X33) = (X33))))),
% 0.81/1.03      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 0.81/1.03  thf('16', plain,
% 0.81/1.03      (![X32 : $i, X33 : $i]:
% 0.81/1.03         (~ (l1_pre_topc @ X32)
% 0.81/1.03          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.81/1.03          | ~ (v3_pre_topc @ X33 @ X32)
% 0.81/1.03          | ((k1_tops_1 @ X32 @ X33) = (X33)))),
% 0.81/1.03      inference('simpl_trail', [status(thm)], ['7', '15'])).
% 0.81/1.03  thf('17', plain,
% 0.81/1.03      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.81/1.03        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.81/1.03        | ~ (l1_pre_topc @ sk_A))),
% 0.81/1.03      inference('sup-', [status(thm)], ['5', '16'])).
% 0.81/1.03  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('19', plain,
% 0.81/1.03      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.81/1.03      inference('demod', [status(thm)], ['17', '18'])).
% 0.81/1.03  thf('20', plain,
% 0.81/1.03      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.81/1.03         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['4', '19'])).
% 0.81/1.03  thf('21', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf(l78_tops_1, axiom,
% 0.81/1.03    (![A:$i]:
% 0.81/1.03     ( ( l1_pre_topc @ A ) =>
% 0.81/1.03       ( ![B:$i]:
% 0.81/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.03           ( ( k2_tops_1 @ A @ B ) =
% 0.81/1.03             ( k7_subset_1 @
% 0.81/1.03               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.81/1.03               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.81/1.03  thf('22', plain,
% 0.81/1.03      (![X30 : $i, X31 : $i]:
% 0.81/1.03         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.81/1.03          | ((k2_tops_1 @ X31 @ X30)
% 0.81/1.03              = (k7_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.81/1.03                 (k2_pre_topc @ X31 @ X30) @ (k1_tops_1 @ X31 @ X30)))
% 0.81/1.03          | ~ (l1_pre_topc @ X31))),
% 0.81/1.03      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.81/1.03  thf('23', plain,
% 0.81/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.81/1.03        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['21', '22'])).
% 0.81/1.03  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('25', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf(dt_k2_pre_topc, axiom,
% 0.81/1.03    (![A:$i,B:$i]:
% 0.81/1.03     ( ( ( l1_pre_topc @ A ) & 
% 0.81/1.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.81/1.03       ( m1_subset_1 @
% 0.81/1.03         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.81/1.03  thf('26', plain,
% 0.81/1.03      (![X28 : $i, X29 : $i]:
% 0.81/1.03         (~ (l1_pre_topc @ X28)
% 0.81/1.03          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.81/1.03          | (m1_subset_1 @ (k2_pre_topc @ X28 @ X29) @ 
% 0.81/1.03             (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 0.81/1.03      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.81/1.03  thf('27', plain,
% 0.81/1.03      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.81/1.03         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.81/1.03        | ~ (l1_pre_topc @ sk_A))),
% 0.81/1.03      inference('sup-', [status(thm)], ['25', '26'])).
% 0.81/1.03  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('29', plain,
% 0.81/1.03      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.81/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.03      inference('demod', [status(thm)], ['27', '28'])).
% 0.81/1.03  thf(redefinition_k7_subset_1, axiom,
% 0.81/1.03    (![A:$i,B:$i,C:$i]:
% 0.81/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.81/1.03       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.81/1.03  thf('30', plain,
% 0.81/1.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.81/1.03         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.81/1.03          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 0.81/1.03      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.81/1.03  thf('31', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.81/1.03           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['29', '30'])).
% 0.81/1.03  thf('32', plain,
% 0.81/1.03      (((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.81/1.03            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.03      inference('demod', [status(thm)], ['23', '24', '31'])).
% 0.81/1.03  thf('33', plain,
% 0.81/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.81/1.03         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.81/1.03      inference('sup+', [status(thm)], ['20', '32'])).
% 0.81/1.03  thf('34', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.81/1.03           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['29', '30'])).
% 0.81/1.03  thf('35', plain,
% 0.81/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.81/1.03         <= (~
% 0.81/1.03             (((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.81/1.03      inference('split', [status(esa)], ['0'])).
% 0.81/1.03  thf('36', plain,
% 0.81/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.81/1.03         <= (~
% 0.81/1.03             (((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['34', '35'])).
% 0.81/1.03  thf('37', plain,
% 0.81/1.03      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.81/1.03         <= (~
% 0.81/1.03             (((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.81/1.03             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['33', '36'])).
% 0.81/1.03  thf('38', plain,
% 0.81/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.81/1.03       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.81/1.03      inference('simplify', [status(thm)], ['37'])).
% 0.81/1.03  thf('39', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.81/1.03      inference('sat_resolution*', [status(thm)], ['2', '38'])).
% 0.81/1.03  thf('40', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.81/1.03      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 0.81/1.03  thf('41', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('42', plain,
% 0.81/1.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.81/1.03         (~ (l1_pre_topc @ X32)
% 0.81/1.03          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.81/1.03          | ((k1_tops_1 @ X35 @ X34) != (X34))
% 0.81/1.03          | (v3_pre_topc @ X34 @ X35)
% 0.81/1.03          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.81/1.03          | ~ (l1_pre_topc @ X35)
% 0.81/1.03          | ~ (v2_pre_topc @ X35))),
% 0.81/1.03      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.81/1.03  thf('43', plain,
% 0.81/1.03      ((![X34 : $i, X35 : $i]:
% 0.81/1.03          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.81/1.03           | ~ (l1_pre_topc @ X35)
% 0.81/1.03           | ~ (v2_pre_topc @ X35)
% 0.81/1.03           | ((k1_tops_1 @ X35 @ X34) != (X34))
% 0.81/1.03           | (v3_pre_topc @ X34 @ X35)))
% 0.81/1.03         <= ((![X34 : $i, X35 : $i]:
% 0.81/1.03                (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.81/1.03                 | ~ (l1_pre_topc @ X35)
% 0.81/1.03                 | ~ (v2_pre_topc @ X35)
% 0.81/1.03                 | ((k1_tops_1 @ X35 @ X34) != (X34))
% 0.81/1.03                 | (v3_pre_topc @ X34 @ X35))))),
% 0.81/1.03      inference('split', [status(esa)], ['42'])).
% 0.81/1.03  thf('44', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('45', plain,
% 0.81/1.03      ((![X32 : $i, X33 : $i]:
% 0.81/1.03          (~ (l1_pre_topc @ X32)
% 0.81/1.03           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))))
% 0.81/1.03         <= ((![X32 : $i, X33 : $i]:
% 0.81/1.03                (~ (l1_pre_topc @ X32)
% 0.81/1.03                 | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32))))))),
% 0.81/1.03      inference('split', [status(esa)], ['42'])).
% 0.81/1.03  thf('46', plain,
% 0.81/1.03      ((~ (l1_pre_topc @ sk_A))
% 0.81/1.03         <= ((![X32 : $i, X33 : $i]:
% 0.81/1.03                (~ (l1_pre_topc @ X32)
% 0.81/1.03                 | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32))))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['44', '45'])).
% 0.81/1.03  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('48', plain,
% 0.81/1.03      (~
% 0.81/1.03       (![X32 : $i, X33 : $i]:
% 0.81/1.03          (~ (l1_pre_topc @ X32)
% 0.81/1.03           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))))),
% 0.81/1.03      inference('demod', [status(thm)], ['46', '47'])).
% 0.81/1.03  thf('49', plain,
% 0.81/1.03      ((![X34 : $i, X35 : $i]:
% 0.81/1.03          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.81/1.03           | ~ (l1_pre_topc @ X35)
% 0.81/1.03           | ~ (v2_pre_topc @ X35)
% 0.81/1.03           | ((k1_tops_1 @ X35 @ X34) != (X34))
% 0.81/1.03           | (v3_pre_topc @ X34 @ X35))) | 
% 0.81/1.03       (![X32 : $i, X33 : $i]:
% 0.81/1.03          (~ (l1_pre_topc @ X32)
% 0.81/1.03           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))))),
% 0.81/1.03      inference('split', [status(esa)], ['42'])).
% 0.81/1.03  thf('50', plain,
% 0.81/1.03      ((![X34 : $i, X35 : $i]:
% 0.81/1.03          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.81/1.03           | ~ (l1_pre_topc @ X35)
% 0.81/1.03           | ~ (v2_pre_topc @ X35)
% 0.81/1.03           | ((k1_tops_1 @ X35 @ X34) != (X34))
% 0.81/1.03           | (v3_pre_topc @ X34 @ X35)))),
% 0.81/1.03      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.81/1.03  thf('51', plain,
% 0.81/1.03      (![X34 : $i, X35 : $i]:
% 0.81/1.03         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.81/1.03          | ~ (l1_pre_topc @ X35)
% 0.81/1.03          | ~ (v2_pre_topc @ X35)
% 0.81/1.03          | ((k1_tops_1 @ X35 @ X34) != (X34))
% 0.81/1.03          | (v3_pre_topc @ X34 @ X35))),
% 0.81/1.03      inference('simpl_trail', [status(thm)], ['43', '50'])).
% 0.81/1.03  thf('52', plain,
% 0.81/1.03      (((v3_pre_topc @ sk_B @ sk_A)
% 0.81/1.03        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 0.81/1.03        | ~ (v2_pre_topc @ sk_A)
% 0.81/1.03        | ~ (l1_pre_topc @ sk_A))),
% 0.81/1.03      inference('sup-', [status(thm)], ['41', '51'])).
% 0.81/1.03  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('55', plain,
% 0.81/1.03      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 0.81/1.03      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.81/1.03  thf(d4_xboole_0, axiom,
% 0.81/1.03    (![A:$i,B:$i,C:$i]:
% 0.81/1.03     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.81/1.03       ( ![D:$i]:
% 0.81/1.03         ( ( r2_hidden @ D @ C ) <=>
% 0.81/1.03           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.81/1.03  thf('56', plain,
% 0.81/1.03      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.81/1.03         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.81/1.03          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.81/1.03          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.81/1.03      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.81/1.03  thf(d10_xboole_0, axiom,
% 0.81/1.03    (![A:$i,B:$i]:
% 0.81/1.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.81/1.03  thf('57', plain,
% 0.81/1.03      (![X14 : $i, X15 : $i]: ((r1_tarski @ X14 @ X15) | ((X14) != (X15)))),
% 0.81/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.03  thf('58', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 0.81/1.03      inference('simplify', [status(thm)], ['57'])).
% 0.81/1.03  thf(t28_xboole_1, axiom,
% 0.81/1.03    (![A:$i,B:$i]:
% 0.81/1.03     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.81/1.03  thf('59', plain,
% 0.81/1.03      (![X19 : $i, X20 : $i]:
% 0.81/1.03         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.81/1.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.81/1.03  thf('60', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['58', '59'])).
% 0.81/1.03  thf(t48_xboole_1, axiom,
% 0.81/1.03    (![A:$i,B:$i]:
% 0.81/1.03     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.81/1.03  thf('61', plain,
% 0.81/1.03      (![X21 : $i, X22 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.81/1.03           = (k3_xboole_0 @ X21 @ X22))),
% 0.81/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/1.03  thf('62', plain,
% 0.81/1.03      (![X21 : $i, X22 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.81/1.03           = (k3_xboole_0 @ X21 @ X22))),
% 0.81/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/1.03  thf('63', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.81/1.03           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.81/1.03      inference('sup+', [status(thm)], ['61', '62'])).
% 0.81/1.03  thf('64', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X0 @ X0)
% 0.81/1.03           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.81/1.03      inference('sup+', [status(thm)], ['60', '63'])).
% 0.81/1.03  thf('65', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['58', '59'])).
% 0.81/1.03  thf(commutativity_k3_xboole_0, axiom,
% 0.81/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.81/1.03  thf('66', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.81/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.81/1.03  thf(t100_xboole_1, axiom,
% 0.81/1.03    (![A:$i,B:$i]:
% 0.81/1.03     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.81/1.03  thf('67', plain,
% 0.81/1.03      (![X17 : $i, X18 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X17 @ X18)
% 0.81/1.03           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.81/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.81/1.03  thf('68', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X0 @ X1)
% 0.81/1.03           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.81/1.03      inference('sup+', [status(thm)], ['66', '67'])).
% 0.81/1.03  thf('69', plain,
% 0.81/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('sup+', [status(thm)], ['65', '68'])).
% 0.81/1.03  thf('70', plain,
% 0.81/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('sup+', [status(thm)], ['65', '68'])).
% 0.81/1.03  thf('71', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((k5_xboole_0 @ X0 @ X0)
% 0.81/1.03           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.81/1.03      inference('demod', [status(thm)], ['64', '69', '70'])).
% 0.81/1.03  thf('72', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.81/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.81/1.03  thf('73', plain,
% 0.81/1.03      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X6 @ X5)
% 0.81/1.03          | (r2_hidden @ X6 @ X4)
% 0.81/1.03          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.81/1.03      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.81/1.03  thf('74', plain,
% 0.81/1.03      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.81/1.03         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.81/1.03      inference('simplify', [status(thm)], ['73'])).
% 0.81/1.03  thf('75', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.81/1.03      inference('sup-', [status(thm)], ['72', '74'])).
% 0.81/1.03  thf('76', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['71', '75'])).
% 0.81/1.03  thf('77', plain,
% 0.81/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('sup+', [status(thm)], ['65', '68'])).
% 0.81/1.03  thf(d5_xboole_0, axiom,
% 0.81/1.03    (![A:$i,B:$i,C:$i]:
% 0.81/1.03     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.81/1.03       ( ![D:$i]:
% 0.81/1.03         ( ( r2_hidden @ D @ C ) <=>
% 0.81/1.03           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.81/1.03  thf('78', plain,
% 0.81/1.03      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X12 @ X11)
% 0.81/1.03          | ~ (r2_hidden @ X12 @ X10)
% 0.81/1.03          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.81/1.03      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.81/1.03  thf('79', plain,
% 0.81/1.03      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X12 @ X10)
% 0.81/1.03          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.81/1.03      inference('simplify', [status(thm)], ['78'])).
% 0.81/1.03  thf('80', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.81/1.03          | ~ (r2_hidden @ X1 @ X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['77', '79'])).
% 0.81/1.03  thf('81', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('clc', [status(thm)], ['76', '80'])).
% 0.81/1.03  thf('82', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.03         ((r2_hidden @ (sk_D @ (k5_xboole_0 @ X0 @ X0) @ X2 @ X1) @ X1)
% 0.81/1.03          | ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X1 @ X2)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['56', '81'])).
% 0.81/1.03  thf('83', plain,
% 0.81/1.03      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.81/1.03         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.81/1.03          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.81/1.03          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.81/1.03      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.81/1.03  thf('84', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('clc', [status(thm)], ['76', '80'])).
% 0.81/1.03  thf('85', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.03         ((r2_hidden @ (sk_D @ (k5_xboole_0 @ X0 @ X0) @ X2 @ X1) @ X2)
% 0.81/1.03          | ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X1 @ X2)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['83', '84'])).
% 0.81/1.03  thf('86', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.81/1.03           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['29', '30'])).
% 0.81/1.03  thf('87', plain,
% 0.81/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.81/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.81/1.03      inference('split', [status(esa)], ['3'])).
% 0.81/1.03  thf('88', plain,
% 0.81/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.81/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.81/1.03      inference('sup+', [status(thm)], ['86', '87'])).
% 0.81/1.03  thf('89', plain,
% 0.81/1.03      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X12 @ X10)
% 0.81/1.03          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.81/1.03      inference('simplify', [status(thm)], ['78'])).
% 0.81/1.03  thf('90', plain,
% 0.81/1.03      ((![X0 : $i]:
% 0.81/1.03          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.81/1.03           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.81/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['88', '89'])).
% 0.81/1.03  thf('91', plain,
% 0.81/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.81/1.03       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.81/1.03      inference('split', [status(esa)], ['3'])).
% 0.81/1.03  thf('92', plain,
% 0.81/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.81/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.03             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.81/1.03      inference('sat_resolution*', [status(thm)], ['2', '38', '91'])).
% 0.81/1.03  thf('93', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.81/1.03          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.81/1.03      inference('simpl_trail', [status(thm)], ['90', '92'])).
% 0.81/1.03  thf('94', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         (((k5_xboole_0 @ X1 @ X1)
% 0.81/1.03            = (k3_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.81/1.03          | ~ (r2_hidden @ 
% 0.81/1.03               (sk_D @ (k5_xboole_0 @ X1 @ X1) @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 0.81/1.03               sk_B))),
% 0.81/1.03      inference('sup-', [status(thm)], ['85', '93'])).
% 0.81/1.03  thf('95', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         (((k5_xboole_0 @ X0 @ X0)
% 0.81/1.03            = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.81/1.03          | ((k5_xboole_0 @ X0 @ X0)
% 0.81/1.03              = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['82', '94'])).
% 0.81/1.03  thf('96', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf(t74_tops_1, axiom,
% 0.81/1.03    (![A:$i]:
% 0.81/1.03     ( ( l1_pre_topc @ A ) =>
% 0.81/1.03       ( ![B:$i]:
% 0.81/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.03           ( ( k1_tops_1 @ A @ B ) =
% 0.81/1.03             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.81/1.03  thf('97', plain,
% 0.81/1.03      (![X36 : $i, X37 : $i]:
% 0.81/1.03         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.81/1.03          | ((k1_tops_1 @ X37 @ X36)
% 0.81/1.03              = (k7_subset_1 @ (u1_struct_0 @ X37) @ X36 @ 
% 0.81/1.03                 (k2_tops_1 @ X37 @ X36)))
% 0.81/1.03          | ~ (l1_pre_topc @ X37))),
% 0.81/1.03      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.81/1.03  thf('98', plain,
% 0.81/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.81/1.03        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.03            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.81/1.03               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['96', '97'])).
% 0.81/1.03  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('100', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('101', plain,
% 0.81/1.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.81/1.03         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.81/1.03          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 0.81/1.03      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.81/1.03  thf('102', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.81/1.03           = (k4_xboole_0 @ sk_B @ X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['100', '101'])).
% 0.81/1.03  thf('103', plain,
% 0.81/1.03      (((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.03         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.03      inference('demod', [status(thm)], ['98', '99', '102'])).
% 0.81/1.03  thf('104', plain,
% 0.81/1.03      (![X21 : $i, X22 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.81/1.03           = (k3_xboole_0 @ X21 @ X22))),
% 0.81/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/1.03  thf('105', plain,
% 0.81/1.03      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.81/1.03         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.03      inference('sup+', [status(thm)], ['103', '104'])).
% 0.81/1.03  thf('106', plain,
% 0.81/1.03      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.81/1.03         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.03      inference('sup+', [status(thm)], ['103', '104'])).
% 0.81/1.03  thf('107', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         (((k5_xboole_0 @ X0 @ X0)
% 0.81/1.03            = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.81/1.03          | ((k5_xboole_0 @ X0 @ X0)
% 0.81/1.03              = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.81/1.03      inference('demod', [status(thm)], ['95', '105', '106'])).
% 0.81/1.03  thf('108', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((k5_xboole_0 @ X0 @ X0)
% 0.81/1.03           = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.03      inference('simplify', [status(thm)], ['107'])).
% 0.81/1.03  thf('109', plain,
% 0.81/1.03      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.81/1.03         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.03      inference('sup+', [status(thm)], ['103', '104'])).
% 0.81/1.03  thf('110', plain,
% 0.81/1.03      (![X17 : $i, X18 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X17 @ X18)
% 0.81/1.03           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.81/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.81/1.03  thf('111', plain,
% 0.81/1.03      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.81/1.03         = (k5_xboole_0 @ sk_B @ 
% 0.81/1.03            (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.81/1.03      inference('sup+', [status(thm)], ['109', '110'])).
% 0.81/1.03  thf('112', plain,
% 0.81/1.03      (((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.03         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.81/1.03      inference('demod', [status(thm)], ['98', '99', '102'])).
% 0.81/1.03  thf('113', plain,
% 0.81/1.03      (((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.03         = (k5_xboole_0 @ sk_B @ 
% 0.81/1.03            (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.81/1.03      inference('demod', [status(thm)], ['111', '112'])).
% 0.81/1.03  thf('114', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.03           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ X0)))),
% 0.81/1.03      inference('sup+', [status(thm)], ['108', '113'])).
% 0.81/1.03  thf('115', plain,
% 0.81/1.03      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.81/1.03         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.81/1.03          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.81/1.03          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.81/1.03      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.81/1.03  thf('116', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.81/1.03          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.81/1.03      inference('eq_fact', [status(thm)], ['115'])).
% 0.81/1.03  thf('117', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('clc', [status(thm)], ['76', '80'])).
% 0.81/1.03  thf('118', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         ((k5_xboole_0 @ X0 @ X0)
% 0.81/1.03           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['116', '117'])).
% 0.81/1.03  thf('119', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.81/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.81/1.03  thf('120', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         ((k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 0.81/1.03           = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('sup+', [status(thm)], ['118', '119'])).
% 0.81/1.03  thf('121', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         ((k5_xboole_0 @ X0 @ X0)
% 0.81/1.03           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['116', '117'])).
% 0.81/1.03  thf('122', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X1) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('sup+', [status(thm)], ['120', '121'])).
% 0.81/1.03  thf('123', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((k5_xboole_0 @ X0 @ X0)
% 0.81/1.03           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.81/1.03      inference('demod', [status(thm)], ['64', '69', '70'])).
% 0.81/1.03  thf('124', plain,
% 0.81/1.03      (![X17 : $i, X18 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X17 @ X18)
% 0.81/1.03           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.81/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.81/1.03  thf('125', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.81/1.03           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.81/1.03      inference('sup+', [status(thm)], ['123', '124'])).
% 0.81/1.03  thf('126', plain,
% 0.81/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('sup+', [status(thm)], ['65', '68'])).
% 0.81/1.03  thf('127', plain,
% 0.81/1.03      (![X21 : $i, X22 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.81/1.03           = (k3_xboole_0 @ X21 @ X22))),
% 0.81/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/1.03  thf('128', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.81/1.03           = (k3_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('sup+', [status(thm)], ['126', '127'])).
% 0.81/1.03  thf('129', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['58', '59'])).
% 0.81/1.03  thf('130', plain,
% 0.81/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.81/1.03      inference('demod', [status(thm)], ['128', '129'])).
% 0.81/1.03  thf('131', plain,
% 0.81/1.03      (![X0 : $i]: ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.81/1.03      inference('sup+', [status(thm)], ['125', '130'])).
% 0.81/1.03  thf('132', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 0.81/1.03      inference('sup+', [status(thm)], ['122', '131'])).
% 0.81/1.03  thf('133', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.81/1.03      inference('demod', [status(thm)], ['114', '132'])).
% 0.81/1.03  thf('134', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.81/1.03      inference('demod', [status(thm)], ['55', '133'])).
% 0.81/1.03  thf('135', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.81/1.03      inference('simplify', [status(thm)], ['134'])).
% 0.81/1.03  thf('136', plain, ($false), inference('demod', [status(thm)], ['40', '135'])).
% 0.81/1.03  
% 0.81/1.03  % SZS output end Refutation
% 0.81/1.03  
% 0.81/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
