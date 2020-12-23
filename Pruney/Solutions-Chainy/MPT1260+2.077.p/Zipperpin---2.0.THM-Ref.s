%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LqJyZXrQuH

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:35 EST 2020

% Result     : Theorem 3.45s
% Output     : Refutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 799 expanded)
%              Number of leaves         :   29 ( 256 expanded)
%              Depth                    :   18
%              Number of atoms          : 1595 (9031 expanded)
%              Number of equality atoms :   96 ( 499 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v3_pre_topc @ X36 @ X35 )
      | ( ( k1_tops_1 @ X35 @ X36 )
        = X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('7',plain,
    ( ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( v3_pre_topc @ X36 @ X35 )
        | ( ( k1_tops_1 @ X35 @ X36 )
          = X36 ) )
   <= ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( v3_pre_topc @ X36 @ X35 )
        | ( ( k1_tops_1 @ X35 @ X36 )
          = X36 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 ) )
   <= ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( v3_pre_topc @ X36 @ X35 )
        | ( ( k1_tops_1 @ X35 @ X36 )
          = X36 ) )
    | ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v3_pre_topc @ X36 @ X35 )
      | ( ( k1_tops_1 @ X35 @ X36 )
        = X36 ) ) ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v3_pre_topc @ X36 @ X35 )
      | ( ( k1_tops_1 @ X35 @ X36 )
        = X36 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_tops_1 @ X34 @ X33 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k2_pre_topc @ X34 @ X33 ) @ ( k1_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k7_subset_1 @ X15 @ X14 @ X16 )
        = ( k4_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','32'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['20','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','39'])).

thf('41',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k1_tops_1 @ X38 @ X37 )
       != X37 )
      | ( v3_pre_topc @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('44',plain,
    ( ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 )
        | ( ( k1_tops_1 @ X38 @ X37 )
         != X37 )
        | ( v3_pre_topc @ X37 @ X38 ) )
   <= ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 )
        | ( ( k1_tops_1 @ X38 @ X37 )
         != X37 )
        | ( v3_pre_topc @ X37 @ X38 ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) )
   <= ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ~ ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 )
        | ( ( k1_tops_1 @ X38 @ X37 )
         != X37 )
        | ( v3_pre_topc @ X37 @ X38 ) )
    | ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('51',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( ( k1_tops_1 @ X38 @ X37 )
       != X37 )
      | ( v3_pre_topc @ X37 @ X38 ) ) ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( ( k1_tops_1 @ X38 @ X37 )
       != X37 )
      | ( v3_pre_topc @ X37 @ X38 ) ) ),
    inference(simpl_trail,[status(thm)],['44','51'])).

thf('53',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('58',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k1_tops_1 @ X40 @ X39 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X40 ) @ X39 @ ( k2_tops_1 @ X40 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k7_subset_1 @ X15 @ X14 @ X16 )
        = ( k4_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('65',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('67',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('68',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('71',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k7_subset_1 @ X15 @ X14 @ X16 )
        = ( k4_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','72'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('74',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('77',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['75','81','82'])).

thf('84',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['64','83'])).

thf('85',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('88',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r1_tarski @ X29 @ ( k2_pre_topc @ X30 @ X29 ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('92',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('95',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('97',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('98',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('100',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['95','98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('102',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('105',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k7_subset_1 @ X15 @ X14 @ X16 )
        = ( k4_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['100','107'])).

thf('109',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['100','107'])).

thf('112',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['110','113','114'])).

thf('116',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['86','115'])).

thf('117',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','32'])).

thf('118',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('119',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('121',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('122',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['95','98','99'])).

thf('124',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('126',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','39','125'])).

thf('127',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['124','126'])).

thf('128',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['119','127'])).

thf('129',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['56','128'])).

thf('130',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['41','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LqJyZXrQuH
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:37:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 3.45/3.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.45/3.70  % Solved by: fo/fo7.sh
% 3.45/3.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.45/3.70  % done 5702 iterations in 3.235s
% 3.45/3.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.45/3.70  % SZS output start Refutation
% 3.45/3.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.45/3.70  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.45/3.70  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.45/3.70  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 3.45/3.70  thf(sk_B_type, type, sk_B: $i).
% 3.45/3.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.45/3.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.45/3.70  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.45/3.70  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 3.45/3.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.45/3.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.45/3.70  thf(sk_A_type, type, sk_A: $i).
% 3.45/3.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.45/3.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.45/3.70  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.45/3.70  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.45/3.70  thf(t76_tops_1, conjecture,
% 3.45/3.70    (![A:$i]:
% 3.45/3.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.45/3.70       ( ![B:$i]:
% 3.45/3.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.45/3.70           ( ( v3_pre_topc @ B @ A ) <=>
% 3.45/3.70             ( ( k2_tops_1 @ A @ B ) =
% 3.45/3.70               ( k7_subset_1 @
% 3.45/3.70                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 3.45/3.70  thf(zf_stmt_0, negated_conjecture,
% 3.45/3.70    (~( ![A:$i]:
% 3.45/3.70        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.45/3.70          ( ![B:$i]:
% 3.45/3.70            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.45/3.70              ( ( v3_pre_topc @ B @ A ) <=>
% 3.45/3.70                ( ( k2_tops_1 @ A @ B ) =
% 3.45/3.70                  ( k7_subset_1 @
% 3.45/3.70                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 3.45/3.70    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 3.45/3.70  thf('0', plain,
% 3.45/3.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 3.45/3.70        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('1', plain,
% 3.45/3.70      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 3.45/3.70      inference('split', [status(esa)], ['0'])).
% 3.45/3.70  thf('2', plain,
% 3.45/3.70      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 3.45/3.70       ~
% 3.45/3.70       (((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 3.45/3.70      inference('split', [status(esa)], ['0'])).
% 3.45/3.70  thf('3', plain,
% 3.45/3.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 3.45/3.70        | (v3_pre_topc @ sk_B @ sk_A))),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('4', plain,
% 3.45/3.70      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.45/3.70      inference('split', [status(esa)], ['3'])).
% 3.45/3.70  thf('5', plain,
% 3.45/3.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf(t55_tops_1, axiom,
% 3.45/3.70    (![A:$i]:
% 3.45/3.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.45/3.70       ( ![B:$i]:
% 3.45/3.70         ( ( l1_pre_topc @ B ) =>
% 3.45/3.70           ( ![C:$i]:
% 3.45/3.70             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.45/3.70               ( ![D:$i]:
% 3.45/3.70                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 3.45/3.70                   ( ( ( v3_pre_topc @ D @ B ) =>
% 3.45/3.70                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 3.45/3.70                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 3.45/3.70                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 3.45/3.70  thf('6', plain,
% 3.45/3.70      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.45/3.70         (~ (l1_pre_topc @ X35)
% 3.45/3.70          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 3.45/3.70          | ~ (v3_pre_topc @ X36 @ X35)
% 3.45/3.70          | ((k1_tops_1 @ X35 @ X36) = (X36))
% 3.45/3.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.45/3.70          | ~ (l1_pre_topc @ X38)
% 3.45/3.70          | ~ (v2_pre_topc @ X38))),
% 3.45/3.70      inference('cnf', [status(esa)], [t55_tops_1])).
% 3.45/3.70  thf('7', plain,
% 3.45/3.70      ((![X35 : $i, X36 : $i]:
% 3.45/3.70          (~ (l1_pre_topc @ X35)
% 3.45/3.70           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 3.45/3.70           | ~ (v3_pre_topc @ X36 @ X35)
% 3.45/3.70           | ((k1_tops_1 @ X35 @ X36) = (X36))))
% 3.45/3.70         <= ((![X35 : $i, X36 : $i]:
% 3.45/3.70                (~ (l1_pre_topc @ X35)
% 3.45/3.70                 | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 3.45/3.70                 | ~ (v3_pre_topc @ X36 @ X35)
% 3.45/3.70                 | ((k1_tops_1 @ X35 @ X36) = (X36)))))),
% 3.45/3.70      inference('split', [status(esa)], ['6'])).
% 3.45/3.70  thf('8', plain,
% 3.45/3.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('9', plain,
% 3.45/3.70      ((![X37 : $i, X38 : $i]:
% 3.45/3.70          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.45/3.70           | ~ (l1_pre_topc @ X38)
% 3.45/3.70           | ~ (v2_pre_topc @ X38)))
% 3.45/3.70         <= ((![X37 : $i, X38 : $i]:
% 3.45/3.70                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.45/3.70                 | ~ (l1_pre_topc @ X38)
% 3.45/3.70                 | ~ (v2_pre_topc @ X38))))),
% 3.45/3.70      inference('split', [status(esa)], ['6'])).
% 3.45/3.70  thf('10', plain,
% 3.45/3.70      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 3.45/3.70         <= ((![X37 : $i, X38 : $i]:
% 3.45/3.70                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.45/3.70                 | ~ (l1_pre_topc @ X38)
% 3.45/3.70                 | ~ (v2_pre_topc @ X38))))),
% 3.45/3.70      inference('sup-', [status(thm)], ['8', '9'])).
% 3.45/3.70  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('13', plain,
% 3.45/3.70      (~
% 3.45/3.70       (![X37 : $i, X38 : $i]:
% 3.45/3.70          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.45/3.70           | ~ (l1_pre_topc @ X38)
% 3.45/3.70           | ~ (v2_pre_topc @ X38)))),
% 3.45/3.70      inference('demod', [status(thm)], ['10', '11', '12'])).
% 3.45/3.70  thf('14', plain,
% 3.45/3.70      ((![X35 : $i, X36 : $i]:
% 3.45/3.70          (~ (l1_pre_topc @ X35)
% 3.45/3.70           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 3.45/3.70           | ~ (v3_pre_topc @ X36 @ X35)
% 3.45/3.70           | ((k1_tops_1 @ X35 @ X36) = (X36)))) | 
% 3.45/3.70       (![X37 : $i, X38 : $i]:
% 3.45/3.70          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.45/3.70           | ~ (l1_pre_topc @ X38)
% 3.45/3.70           | ~ (v2_pre_topc @ X38)))),
% 3.45/3.70      inference('split', [status(esa)], ['6'])).
% 3.45/3.70  thf('15', plain,
% 3.45/3.70      ((![X35 : $i, X36 : $i]:
% 3.45/3.70          (~ (l1_pre_topc @ X35)
% 3.45/3.70           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 3.45/3.70           | ~ (v3_pre_topc @ X36 @ X35)
% 3.45/3.70           | ((k1_tops_1 @ X35 @ X36) = (X36))))),
% 3.45/3.70      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 3.45/3.70  thf('16', plain,
% 3.45/3.70      (![X35 : $i, X36 : $i]:
% 3.45/3.70         (~ (l1_pre_topc @ X35)
% 3.45/3.70          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 3.45/3.70          | ~ (v3_pre_topc @ X36 @ X35)
% 3.45/3.70          | ((k1_tops_1 @ X35 @ X36) = (X36)))),
% 3.45/3.70      inference('simpl_trail', [status(thm)], ['7', '15'])).
% 3.45/3.70  thf('17', plain,
% 3.45/3.70      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 3.45/3.70        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 3.45/3.70        | ~ (l1_pre_topc @ sk_A))),
% 3.45/3.70      inference('sup-', [status(thm)], ['5', '16'])).
% 3.45/3.70  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('19', plain,
% 3.45/3.70      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 3.45/3.70      inference('demod', [status(thm)], ['17', '18'])).
% 3.45/3.70  thf('20', plain,
% 3.45/3.70      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 3.45/3.70         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.45/3.70      inference('sup-', [status(thm)], ['4', '19'])).
% 3.45/3.70  thf('21', plain,
% 3.45/3.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf(l78_tops_1, axiom,
% 3.45/3.70    (![A:$i]:
% 3.45/3.70     ( ( l1_pre_topc @ A ) =>
% 3.45/3.70       ( ![B:$i]:
% 3.45/3.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.45/3.70           ( ( k2_tops_1 @ A @ B ) =
% 3.45/3.70             ( k7_subset_1 @
% 3.45/3.70               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 3.45/3.70               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.45/3.70  thf('22', plain,
% 3.45/3.70      (![X33 : $i, X34 : $i]:
% 3.45/3.70         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 3.45/3.70          | ((k2_tops_1 @ X34 @ X33)
% 3.45/3.70              = (k7_subset_1 @ (u1_struct_0 @ X34) @ 
% 3.45/3.70                 (k2_pre_topc @ X34 @ X33) @ (k1_tops_1 @ X34 @ X33)))
% 3.45/3.70          | ~ (l1_pre_topc @ X34))),
% 3.45/3.70      inference('cnf', [status(esa)], [l78_tops_1])).
% 3.45/3.70  thf('23', plain,
% 3.45/3.70      ((~ (l1_pre_topc @ sk_A)
% 3.45/3.70        | ((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 3.45/3.70      inference('sup-', [status(thm)], ['21', '22'])).
% 3.45/3.70  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('25', plain,
% 3.45/3.70      (((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70            (k1_tops_1 @ sk_A @ sk_B)))),
% 3.45/3.70      inference('demod', [status(thm)], ['23', '24'])).
% 3.45/3.70  thf('26', plain,
% 3.45/3.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf(dt_k2_pre_topc, axiom,
% 3.45/3.70    (![A:$i,B:$i]:
% 3.45/3.70     ( ( ( l1_pre_topc @ A ) & 
% 3.45/3.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.45/3.70       ( m1_subset_1 @
% 3.45/3.70         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.45/3.70  thf('27', plain,
% 3.45/3.70      (![X27 : $i, X28 : $i]:
% 3.45/3.70         (~ (l1_pre_topc @ X27)
% 3.45/3.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 3.45/3.70          | (m1_subset_1 @ (k2_pre_topc @ X27 @ X28) @ 
% 3.45/3.70             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 3.45/3.70      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 3.45/3.70  thf('28', plain,
% 3.45/3.70      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.45/3.70        | ~ (l1_pre_topc @ sk_A))),
% 3.45/3.70      inference('sup-', [status(thm)], ['26', '27'])).
% 3.45/3.70  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('30', plain,
% 3.45/3.70      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.70      inference('demod', [status(thm)], ['28', '29'])).
% 3.45/3.70  thf(redefinition_k7_subset_1, axiom,
% 3.45/3.70    (![A:$i,B:$i,C:$i]:
% 3.45/3.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.45/3.70       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 3.45/3.70  thf('31', plain,
% 3.45/3.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.45/3.70         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 3.45/3.70          | ((k7_subset_1 @ X15 @ X14 @ X16) = (k4_xboole_0 @ X14 @ X16)))),
% 3.45/3.70      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.45/3.70  thf('32', plain,
% 3.45/3.70      (![X0 : $i]:
% 3.45/3.70         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 3.45/3.70      inference('sup-', [status(thm)], ['30', '31'])).
% 3.45/3.70  thf('33', plain,
% 3.45/3.70      (((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70            (k1_tops_1 @ sk_A @ sk_B)))),
% 3.45/3.70      inference('demod', [status(thm)], ['25', '32'])).
% 3.45/3.70  thf('34', plain,
% 3.45/3.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 3.45/3.70         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.45/3.70      inference('sup+', [status(thm)], ['20', '33'])).
% 3.45/3.70  thf('35', plain,
% 3.45/3.70      (![X0 : $i]:
% 3.45/3.70         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 3.45/3.70      inference('sup-', [status(thm)], ['30', '31'])).
% 3.45/3.70  thf('36', plain,
% 3.45/3.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 3.45/3.70         <= (~
% 3.45/3.70             (((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.45/3.70      inference('split', [status(esa)], ['0'])).
% 3.45/3.70  thf('37', plain,
% 3.45/3.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 3.45/3.70         <= (~
% 3.45/3.70             (((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.45/3.70      inference('sup-', [status(thm)], ['35', '36'])).
% 3.45/3.70  thf('38', plain,
% 3.45/3.70      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 3.45/3.70         <= (~
% 3.45/3.70             (((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 3.45/3.70             ((v3_pre_topc @ sk_B @ sk_A)))),
% 3.45/3.70      inference('sup-', [status(thm)], ['34', '37'])).
% 3.45/3.70  thf('39', plain,
% 3.45/3.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 3.45/3.70       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 3.45/3.70      inference('simplify', [status(thm)], ['38'])).
% 3.45/3.70  thf('40', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 3.45/3.70      inference('sat_resolution*', [status(thm)], ['2', '39'])).
% 3.45/3.70  thf('41', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 3.45/3.70      inference('simpl_trail', [status(thm)], ['1', '40'])).
% 3.45/3.70  thf('42', plain,
% 3.45/3.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('43', plain,
% 3.45/3.70      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.45/3.70         (~ (l1_pre_topc @ X35)
% 3.45/3.70          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 3.45/3.70          | ((k1_tops_1 @ X38 @ X37) != (X37))
% 3.45/3.70          | (v3_pre_topc @ X37 @ X38)
% 3.45/3.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.45/3.70          | ~ (l1_pre_topc @ X38)
% 3.45/3.70          | ~ (v2_pre_topc @ X38))),
% 3.45/3.70      inference('cnf', [status(esa)], [t55_tops_1])).
% 3.45/3.70  thf('44', plain,
% 3.45/3.70      ((![X37 : $i, X38 : $i]:
% 3.45/3.70          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.45/3.70           | ~ (l1_pre_topc @ X38)
% 3.45/3.70           | ~ (v2_pre_topc @ X38)
% 3.45/3.70           | ((k1_tops_1 @ X38 @ X37) != (X37))
% 3.45/3.70           | (v3_pre_topc @ X37 @ X38)))
% 3.45/3.70         <= ((![X37 : $i, X38 : $i]:
% 3.45/3.70                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.45/3.70                 | ~ (l1_pre_topc @ X38)
% 3.45/3.70                 | ~ (v2_pre_topc @ X38)
% 3.45/3.70                 | ((k1_tops_1 @ X38 @ X37) != (X37))
% 3.45/3.70                 | (v3_pre_topc @ X37 @ X38))))),
% 3.45/3.70      inference('split', [status(esa)], ['43'])).
% 3.45/3.70  thf('45', plain,
% 3.45/3.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('46', plain,
% 3.45/3.70      ((![X35 : $i, X36 : $i]:
% 3.45/3.70          (~ (l1_pre_topc @ X35)
% 3.45/3.70           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))))
% 3.45/3.70         <= ((![X35 : $i, X36 : $i]:
% 3.45/3.70                (~ (l1_pre_topc @ X35)
% 3.45/3.70                 | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35))))))),
% 3.45/3.70      inference('split', [status(esa)], ['43'])).
% 3.45/3.70  thf('47', plain,
% 3.45/3.70      ((~ (l1_pre_topc @ sk_A))
% 3.45/3.70         <= ((![X35 : $i, X36 : $i]:
% 3.45/3.70                (~ (l1_pre_topc @ X35)
% 3.45/3.70                 | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35))))))),
% 3.45/3.70      inference('sup-', [status(thm)], ['45', '46'])).
% 3.45/3.70  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('49', plain,
% 3.45/3.70      (~
% 3.45/3.70       (![X35 : $i, X36 : $i]:
% 3.45/3.70          (~ (l1_pre_topc @ X35)
% 3.45/3.70           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))))),
% 3.45/3.70      inference('demod', [status(thm)], ['47', '48'])).
% 3.45/3.70  thf('50', plain,
% 3.45/3.70      ((![X37 : $i, X38 : $i]:
% 3.45/3.70          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.45/3.70           | ~ (l1_pre_topc @ X38)
% 3.45/3.70           | ~ (v2_pre_topc @ X38)
% 3.45/3.70           | ((k1_tops_1 @ X38 @ X37) != (X37))
% 3.45/3.70           | (v3_pre_topc @ X37 @ X38))) | 
% 3.45/3.70       (![X35 : $i, X36 : $i]:
% 3.45/3.70          (~ (l1_pre_topc @ X35)
% 3.45/3.70           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))))),
% 3.45/3.70      inference('split', [status(esa)], ['43'])).
% 3.45/3.70  thf('51', plain,
% 3.45/3.70      ((![X37 : $i, X38 : $i]:
% 3.45/3.70          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.45/3.70           | ~ (l1_pre_topc @ X38)
% 3.45/3.70           | ~ (v2_pre_topc @ X38)
% 3.45/3.70           | ((k1_tops_1 @ X38 @ X37) != (X37))
% 3.45/3.70           | (v3_pre_topc @ X37 @ X38)))),
% 3.45/3.70      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 3.45/3.70  thf('52', plain,
% 3.45/3.70      (![X37 : $i, X38 : $i]:
% 3.45/3.70         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.45/3.70          | ~ (l1_pre_topc @ X38)
% 3.45/3.70          | ~ (v2_pre_topc @ X38)
% 3.45/3.70          | ((k1_tops_1 @ X38 @ X37) != (X37))
% 3.45/3.70          | (v3_pre_topc @ X37 @ X38))),
% 3.45/3.70      inference('simpl_trail', [status(thm)], ['44', '51'])).
% 3.45/3.70  thf('53', plain,
% 3.45/3.70      (((v3_pre_topc @ sk_B @ sk_A)
% 3.45/3.70        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 3.45/3.70        | ~ (v2_pre_topc @ sk_A)
% 3.45/3.70        | ~ (l1_pre_topc @ sk_A))),
% 3.45/3.70      inference('sup-', [status(thm)], ['42', '52'])).
% 3.45/3.70  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('56', plain,
% 3.45/3.70      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 3.45/3.70      inference('demod', [status(thm)], ['53', '54', '55'])).
% 3.45/3.70  thf('57', plain,
% 3.45/3.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf(t74_tops_1, axiom,
% 3.45/3.70    (![A:$i]:
% 3.45/3.70     ( ( l1_pre_topc @ A ) =>
% 3.45/3.70       ( ![B:$i]:
% 3.45/3.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.45/3.70           ( ( k1_tops_1 @ A @ B ) =
% 3.45/3.70             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.45/3.70  thf('58', plain,
% 3.45/3.70      (![X39 : $i, X40 : $i]:
% 3.45/3.70         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 3.45/3.70          | ((k1_tops_1 @ X40 @ X39)
% 3.45/3.70              = (k7_subset_1 @ (u1_struct_0 @ X40) @ X39 @ 
% 3.45/3.70                 (k2_tops_1 @ X40 @ X39)))
% 3.45/3.70          | ~ (l1_pre_topc @ X40))),
% 3.45/3.70      inference('cnf', [status(esa)], [t74_tops_1])).
% 3.45/3.70  thf('59', plain,
% 3.45/3.70      ((~ (l1_pre_topc @ sk_A)
% 3.45/3.70        | ((k1_tops_1 @ sk_A @ sk_B)
% 3.45/3.70            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.45/3.70               (k2_tops_1 @ sk_A @ sk_B))))),
% 3.45/3.70      inference('sup-', [status(thm)], ['57', '58'])).
% 3.45/3.70  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('61', plain,
% 3.45/3.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('62', plain,
% 3.45/3.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.45/3.70         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 3.45/3.70          | ((k7_subset_1 @ X15 @ X14 @ X16) = (k4_xboole_0 @ X14 @ X16)))),
% 3.45/3.70      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.45/3.70  thf('63', plain,
% 3.45/3.70      (![X0 : $i]:
% 3.45/3.70         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.45/3.70           = (k4_xboole_0 @ sk_B @ X0))),
% 3.45/3.70      inference('sup-', [status(thm)], ['61', '62'])).
% 3.45/3.70  thf('64', plain,
% 3.45/3.70      (((k1_tops_1 @ sk_A @ sk_B)
% 3.45/3.70         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.45/3.70      inference('demod', [status(thm)], ['59', '60', '63'])).
% 3.45/3.70  thf(dt_k2_subset_1, axiom,
% 3.45/3.70    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 3.45/3.70  thf('65', plain,
% 3.45/3.70      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 3.45/3.70      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 3.45/3.70  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 3.45/3.70  thf('66', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 3.45/3.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 3.45/3.70  thf('67', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 3.45/3.70      inference('demod', [status(thm)], ['65', '66'])).
% 3.45/3.70  thf(dt_k7_subset_1, axiom,
% 3.45/3.70    (![A:$i,B:$i,C:$i]:
% 3.45/3.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.45/3.70       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.45/3.70  thf('68', plain,
% 3.45/3.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.45/3.70         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 3.45/3.70          | (m1_subset_1 @ (k7_subset_1 @ X7 @ X6 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 3.45/3.70      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 3.45/3.70  thf('69', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         (m1_subset_1 @ (k7_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.45/3.70      inference('sup-', [status(thm)], ['67', '68'])).
% 3.45/3.70  thf('70', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 3.45/3.70      inference('demod', [status(thm)], ['65', '66'])).
% 3.45/3.70  thf('71', plain,
% 3.45/3.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.45/3.70         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 3.45/3.70          | ((k7_subset_1 @ X15 @ X14 @ X16) = (k4_xboole_0 @ X14 @ X16)))),
% 3.45/3.70      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.45/3.70  thf('72', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 3.45/3.70      inference('sup-', [status(thm)], ['70', '71'])).
% 3.45/3.70  thf('73', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.45/3.70      inference('demod', [status(thm)], ['69', '72'])).
% 3.45/3.70  thf(involutiveness_k3_subset_1, axiom,
% 3.45/3.70    (![A:$i,B:$i]:
% 3.45/3.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.45/3.70       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 3.45/3.70  thf('74', plain,
% 3.45/3.70      (![X12 : $i, X13 : $i]:
% 3.45/3.70         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 3.45/3.70          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 3.45/3.70      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 3.45/3.70  thf('75', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 3.45/3.70           = (k4_xboole_0 @ X0 @ X1))),
% 3.45/3.70      inference('sup-', [status(thm)], ['73', '74'])).
% 3.45/3.70  thf('76', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         (m1_subset_1 @ (k7_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.45/3.70      inference('sup-', [status(thm)], ['67', '68'])).
% 3.45/3.70  thf(d5_subset_1, axiom,
% 3.45/3.70    (![A:$i,B:$i]:
% 3.45/3.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.45/3.70       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 3.45/3.70  thf('77', plain,
% 3.45/3.70      (![X1 : $i, X2 : $i]:
% 3.45/3.70         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 3.45/3.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 3.45/3.70      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.45/3.70  thf('78', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         ((k3_subset_1 @ X0 @ (k7_subset_1 @ X0 @ X0 @ X1))
% 3.45/3.70           = (k4_xboole_0 @ X0 @ (k7_subset_1 @ X0 @ X0 @ X1)))),
% 3.45/3.70      inference('sup-', [status(thm)], ['76', '77'])).
% 3.45/3.70  thf('79', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 3.45/3.70      inference('sup-', [status(thm)], ['70', '71'])).
% 3.45/3.70  thf('80', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 3.45/3.70      inference('sup-', [status(thm)], ['70', '71'])).
% 3.45/3.70  thf('81', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.45/3.70           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 3.45/3.70      inference('demod', [status(thm)], ['78', '79', '80'])).
% 3.45/3.70  thf('82', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.45/3.70           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 3.45/3.70      inference('demod', [status(thm)], ['78', '79', '80'])).
% 3.45/3.70  thf('83', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 3.45/3.70           = (k4_xboole_0 @ X0 @ X1))),
% 3.45/3.70      inference('demod', [status(thm)], ['75', '81', '82'])).
% 3.45/3.70  thf('84', plain,
% 3.45/3.70      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 3.45/3.70         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.45/3.70      inference('sup+', [status(thm)], ['64', '83'])).
% 3.45/3.70  thf('85', plain,
% 3.45/3.70      (((k1_tops_1 @ sk_A @ sk_B)
% 3.45/3.70         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.45/3.70      inference('demod', [status(thm)], ['59', '60', '63'])).
% 3.45/3.70  thf('86', plain,
% 3.45/3.70      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 3.45/3.70         = (k1_tops_1 @ sk_A @ sk_B))),
% 3.45/3.70      inference('demod', [status(thm)], ['84', '85'])).
% 3.45/3.70  thf('87', plain,
% 3.45/3.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf(t48_pre_topc, axiom,
% 3.45/3.70    (![A:$i]:
% 3.45/3.70     ( ( l1_pre_topc @ A ) =>
% 3.45/3.70       ( ![B:$i]:
% 3.45/3.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.45/3.70           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 3.45/3.70  thf('88', plain,
% 3.45/3.70      (![X29 : $i, X30 : $i]:
% 3.45/3.70         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 3.45/3.70          | (r1_tarski @ X29 @ (k2_pre_topc @ X30 @ X29))
% 3.45/3.70          | ~ (l1_pre_topc @ X30))),
% 3.45/3.70      inference('cnf', [status(esa)], [t48_pre_topc])).
% 3.45/3.70  thf('89', plain,
% 3.45/3.70      ((~ (l1_pre_topc @ sk_A)
% 3.45/3.70        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 3.45/3.70      inference('sup-', [status(thm)], ['87', '88'])).
% 3.45/3.70  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.70  thf('91', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 3.45/3.70      inference('demod', [status(thm)], ['89', '90'])).
% 3.45/3.70  thf(t3_subset, axiom,
% 3.45/3.70    (![A:$i,B:$i]:
% 3.45/3.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.45/3.70  thf('92', plain,
% 3.45/3.70      (![X21 : $i, X23 : $i]:
% 3.45/3.70         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 3.45/3.70      inference('cnf', [status(esa)], [t3_subset])).
% 3.45/3.70  thf('93', plain,
% 3.45/3.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 3.45/3.70      inference('sup-', [status(thm)], ['91', '92'])).
% 3.45/3.70  thf('94', plain,
% 3.45/3.70      (![X12 : $i, X13 : $i]:
% 3.45/3.70         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 3.45/3.70          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 3.45/3.70      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 3.45/3.70  thf('95', plain,
% 3.45/3.70      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 3.45/3.70      inference('sup-', [status(thm)], ['93', '94'])).
% 3.45/3.70  thf('96', plain,
% 3.45/3.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 3.45/3.70      inference('sup-', [status(thm)], ['91', '92'])).
% 3.45/3.70  thf('97', plain,
% 3.45/3.70      (![X1 : $i, X2 : $i]:
% 3.45/3.70         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 3.45/3.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 3.45/3.70      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.45/3.70  thf('98', plain,
% 3.45/3.70      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 3.45/3.70         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 3.45/3.70      inference('sup-', [status(thm)], ['96', '97'])).
% 3.45/3.70  thf('99', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.45/3.70           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 3.45/3.70      inference('demod', [status(thm)], ['78', '79', '80'])).
% 3.45/3.70  thf('100', plain,
% 3.45/3.70      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 3.45/3.70      inference('demod', [status(thm)], ['95', '98', '99'])).
% 3.45/3.70  thf('101', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.45/3.70      inference('demod', [status(thm)], ['69', '72'])).
% 3.45/3.70  thf('102', plain,
% 3.45/3.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.45/3.70         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 3.45/3.70          | (m1_subset_1 @ (k7_subset_1 @ X7 @ X6 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 3.45/3.70      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 3.45/3.70  thf('103', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.70         (m1_subset_1 @ (k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ 
% 3.45/3.70          (k1_zfmisc_1 @ X0))),
% 3.45/3.70      inference('sup-', [status(thm)], ['101', '102'])).
% 3.45/3.70  thf('104', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.45/3.70      inference('demod', [status(thm)], ['69', '72'])).
% 3.45/3.70  thf('105', plain,
% 3.45/3.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.45/3.70         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 3.45/3.70          | ((k7_subset_1 @ X15 @ X14 @ X16) = (k4_xboole_0 @ X14 @ X16)))),
% 3.45/3.70      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.45/3.70  thf('106', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.70         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 3.45/3.70           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 3.45/3.70      inference('sup-', [status(thm)], ['104', '105'])).
% 3.45/3.70  thf('107', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.70         (m1_subset_1 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ 
% 3.45/3.70          (k1_zfmisc_1 @ X0))),
% 3.45/3.70      inference('demod', [status(thm)], ['103', '106'])).
% 3.45/3.70  thf('108', plain,
% 3.45/3.70      (![X0 : $i]:
% 3.45/3.70         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 3.45/3.70          (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 3.45/3.70      inference('sup+', [status(thm)], ['100', '107'])).
% 3.45/3.70  thf('109', plain,
% 3.45/3.70      (![X12 : $i, X13 : $i]:
% 3.45/3.70         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 3.45/3.70          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 3.45/3.70      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 3.45/3.70  thf('110', plain,
% 3.45/3.70      (![X0 : $i]:
% 3.45/3.70         ((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70           (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70            (k4_xboole_0 @ sk_B @ X0)))
% 3.45/3.70           = (k4_xboole_0 @ sk_B @ X0))),
% 3.45/3.70      inference('sup-', [status(thm)], ['108', '109'])).
% 3.45/3.70  thf('111', plain,
% 3.45/3.70      (![X0 : $i]:
% 3.45/3.70         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 3.45/3.70          (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 3.45/3.70      inference('sup+', [status(thm)], ['100', '107'])).
% 3.45/3.70  thf('112', plain,
% 3.45/3.70      (![X1 : $i, X2 : $i]:
% 3.45/3.70         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 3.45/3.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 3.45/3.70      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.45/3.70  thf('113', plain,
% 3.45/3.70      (![X0 : $i]:
% 3.45/3.70         ((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70           (k4_xboole_0 @ sk_B @ X0))
% 3.45/3.70           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70              (k4_xboole_0 @ sk_B @ X0)))),
% 3.45/3.70      inference('sup-', [status(thm)], ['111', '112'])).
% 3.45/3.70  thf('114', plain,
% 3.45/3.70      (![X0 : $i, X1 : $i]:
% 3.45/3.70         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.45/3.70           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 3.45/3.70      inference('demod', [status(thm)], ['78', '79', '80'])).
% 3.45/3.70  thf('115', plain,
% 3.45/3.70      (![X0 : $i]:
% 3.45/3.70         ((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70           (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70            (k4_xboole_0 @ sk_B @ X0)))
% 3.45/3.70           = (k4_xboole_0 @ sk_B @ X0))),
% 3.45/3.70      inference('demod', [status(thm)], ['110', '113', '114'])).
% 3.45/3.70  thf('116', plain,
% 3.45/3.70      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))
% 3.45/3.70         = (k4_xboole_0 @ sk_B @ 
% 3.45/3.70            (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 3.45/3.70      inference('sup+', [status(thm)], ['86', '115'])).
% 3.45/3.70  thf('117', plain,
% 3.45/3.70      (((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70            (k1_tops_1 @ sk_A @ sk_B)))),
% 3.45/3.70      inference('demod', [status(thm)], ['25', '32'])).
% 3.45/3.70  thf('118', plain,
% 3.45/3.70      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 3.45/3.70         = (k1_tops_1 @ sk_A @ sk_B))),
% 3.45/3.70      inference('demod', [status(thm)], ['84', '85'])).
% 3.45/3.70  thf('119', plain,
% 3.45/3.70      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 3.45/3.70         = (k1_tops_1 @ sk_A @ sk_B))),
% 3.45/3.70      inference('demod', [status(thm)], ['116', '117', '118'])).
% 3.45/3.70  thf('120', plain,
% 3.45/3.70      (![X0 : $i]:
% 3.45/3.70         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 3.45/3.70      inference('sup-', [status(thm)], ['30', '31'])).
% 3.45/3.70  thf('121', plain,
% 3.45/3.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 3.45/3.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.45/3.70      inference('split', [status(esa)], ['3'])).
% 3.45/3.70  thf('122', plain,
% 3.45/3.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 3.45/3.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.45/3.70      inference('sup+', [status(thm)], ['120', '121'])).
% 3.45/3.70  thf('123', plain,
% 3.45/3.70      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.45/3.70         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 3.45/3.70      inference('demod', [status(thm)], ['95', '98', '99'])).
% 3.45/3.70  thf('124', plain,
% 3.45/3.70      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 3.45/3.70          = (sk_B)))
% 3.45/3.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.45/3.70      inference('sup+', [status(thm)], ['122', '123'])).
% 3.45/3.70  thf('125', plain,
% 3.45/3.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 3.45/3.70       ((v3_pre_topc @ sk_B @ sk_A))),
% 3.45/3.70      inference('split', [status(esa)], ['3'])).
% 3.45/3.70  thf('126', plain,
% 3.45/3.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.45/3.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.70             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 3.45/3.70      inference('sat_resolution*', [status(thm)], ['2', '39', '125'])).
% 3.45/3.70  thf('127', plain,
% 3.45/3.70      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 3.45/3.70         = (sk_B))),
% 3.45/3.70      inference('simpl_trail', [status(thm)], ['124', '126'])).
% 3.45/3.70  thf('128', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 3.45/3.70      inference('sup+', [status(thm)], ['119', '127'])).
% 3.45/3.70  thf('129', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 3.45/3.70      inference('demod', [status(thm)], ['56', '128'])).
% 3.45/3.70  thf('130', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 3.45/3.70      inference('simplify', [status(thm)], ['129'])).
% 3.45/3.70  thf('131', plain, ($false), inference('demod', [status(thm)], ['41', '130'])).
% 3.45/3.70  
% 3.45/3.70  % SZS output end Refutation
% 3.45/3.70  
% 3.54/3.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
