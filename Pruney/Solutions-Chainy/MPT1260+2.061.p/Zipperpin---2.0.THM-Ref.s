%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fgDxq8013S

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:32 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 298 expanded)
%              Number of leaves         :   27 (  91 expanded)
%              Depth                    :   18
%              Number of atoms          : 1132 (4423 expanded)
%              Number of equality atoms :   68 ( 220 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X20 )
      | ( ( k1_tops_1 @ X20 @ X21 )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('7',plain,
    ( ! [X20: $i,X21: $i] :
        ( ~ ( l1_pre_topc @ X20 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( v3_pre_topc @ X21 @ X20 )
        | ( ( k1_tops_1 @ X20 @ X21 )
          = X21 ) )
   <= ! [X20: $i,X21: $i] :
        ( ~ ( l1_pre_topc @ X20 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( v3_pre_topc @ X21 @ X20 )
        | ( ( k1_tops_1 @ X20 @ X21 )
          = X21 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X22: $i,X23: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( l1_pre_topc @ X23 )
        | ~ ( v2_pre_topc @ X23 ) )
   <= ! [X22: $i,X23: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( l1_pre_topc @ X23 )
        | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X22: $i,X23: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( l1_pre_topc @ X23 )
        | ~ ( v2_pre_topc @ X23 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ! [X22: $i,X23: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( l1_pre_topc @ X23 )
        | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ! [X20: $i,X21: $i] :
        ( ~ ( l1_pre_topc @ X20 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( v3_pre_topc @ X21 @ X20 )
        | ( ( k1_tops_1 @ X20 @ X21 )
          = X21 ) )
    | ! [X22: $i,X23: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( l1_pre_topc @ X23 )
        | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X20 )
      | ( ( k1_tops_1 @ X20 @ X21 )
        = X21 ) ) ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X20 )
      | ( ( k1_tops_1 @ X20 @ X21 )
        = X21 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_tops_1 @ X19 @ X18 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k2_pre_topc @ X19 @ X18 ) @ ( k1_tops_1 @ X19 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k1_tops_1 @ X23 @ X22 )
       != X22 )
      | ( v3_pre_topc @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('43',plain,
    ( ! [X22: $i,X23: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( l1_pre_topc @ X23 )
        | ~ ( v2_pre_topc @ X23 )
        | ( ( k1_tops_1 @ X23 @ X22 )
         != X22 )
        | ( v3_pre_topc @ X22 @ X23 ) )
   <= ! [X22: $i,X23: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( l1_pre_topc @ X23 )
        | ~ ( v2_pre_topc @ X23 )
        | ( ( k1_tops_1 @ X23 @ X22 )
         != X22 )
        | ( v3_pre_topc @ X22 @ X23 ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ! [X20: $i,X21: $i] :
        ( ~ ( l1_pre_topc @ X20 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
   <= ! [X20: $i,X21: $i] :
        ( ~ ( l1_pre_topc @ X20 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X20: $i,X21: $i] :
        ( ~ ( l1_pre_topc @ X20 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ! [X20: $i,X21: $i] :
        ( ~ ( l1_pre_topc @ X20 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X22: $i,X23: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( l1_pre_topc @ X23 )
        | ~ ( v2_pre_topc @ X23 )
        | ( ( k1_tops_1 @ X23 @ X22 )
         != X22 )
        | ( v3_pre_topc @ X22 @ X23 ) )
    | ! [X20: $i,X21: $i] :
        ( ~ ( l1_pre_topc @ X20 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( ( k1_tops_1 @ X23 @ X22 )
       != X22 )
      | ( v3_pre_topc @ X22 @ X23 ) ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( ( k1_tops_1 @ X23 @ X22 )
       != X22 )
      | ( v3_pre_topc @ X22 @ X23 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k1_tops_1 @ X27 @ X26 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ ( k2_tops_1 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
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

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('67',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ X14 @ ( k2_pre_topc @ X15 @ X14 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['70','71'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t89_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) )).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t89_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('76',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['70','71'])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['65','80'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('83',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','38','82'])).

thf('84',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['81','83'])).

thf('85',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['58','59','62','84'])).

thf('86',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['55','85'])).

thf('87',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['40','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fgDxq8013S
% 0.16/0.36  % Computer   : n010.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 13:10:30 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 172 iterations in 0.123s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.60  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.41/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.41/0.60  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.41/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.41/0.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(t76_tops_1, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( ( v3_pre_topc @ B @ A ) <=>
% 0.41/0.60             ( ( k2_tops_1 @ A @ B ) =
% 0.41/0.60               ( k7_subset_1 @
% 0.41/0.60                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60              ( ( v3_pre_topc @ B @ A ) <=>
% 0.41/0.60                ( ( k2_tops_1 @ A @ B ) =
% 0.41/0.60                  ( k7_subset_1 @
% 0.41/0.60                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.41/0.60        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.41/0.60       ~
% 0.41/0.60       (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.41/0.60        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t55_tops_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( l1_pre_topc @ B ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60               ( ![D:$i]:
% 0.41/0.60                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.60                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.41/0.60                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.41/0.60                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.41/0.60                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X20)
% 0.41/0.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.41/0.60          | ~ (v3_pre_topc @ X21 @ X20)
% 0.41/0.60          | ((k1_tops_1 @ X20 @ X21) = (X21))
% 0.41/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.41/0.60          | ~ (l1_pre_topc @ X23)
% 0.41/0.60          | ~ (v2_pre_topc @ X23))),
% 0.41/0.60      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      ((![X20 : $i, X21 : $i]:
% 0.41/0.60          (~ (l1_pre_topc @ X20)
% 0.41/0.60           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.41/0.60           | ~ (v3_pre_topc @ X21 @ X20)
% 0.41/0.60           | ((k1_tops_1 @ X20 @ X21) = (X21))))
% 0.41/0.60         <= ((![X20 : $i, X21 : $i]:
% 0.41/0.60                (~ (l1_pre_topc @ X20)
% 0.41/0.60                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.41/0.60                 | ~ (v3_pre_topc @ X21 @ X20)
% 0.41/0.60                 | ((k1_tops_1 @ X20 @ X21) = (X21)))))),
% 0.41/0.60      inference('split', [status(esa)], ['6'])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      ((![X22 : $i, X23 : $i]:
% 0.41/0.60          (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.41/0.60           | ~ (l1_pre_topc @ X23)
% 0.41/0.60           | ~ (v2_pre_topc @ X23)))
% 0.41/0.60         <= ((![X22 : $i, X23 : $i]:
% 0.41/0.60                (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.41/0.60                 | ~ (l1_pre_topc @ X23)
% 0.41/0.60                 | ~ (v2_pre_topc @ X23))))),
% 0.41/0.60      inference('split', [status(esa)], ['6'])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.41/0.60         <= ((![X22 : $i, X23 : $i]:
% 0.41/0.60                (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.41/0.60                 | ~ (l1_pre_topc @ X23)
% 0.41/0.60                 | ~ (v2_pre_topc @ X23))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.60  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (~
% 0.41/0.60       (![X22 : $i, X23 : $i]:
% 0.41/0.60          (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.41/0.60           | ~ (l1_pre_topc @ X23)
% 0.41/0.60           | ~ (v2_pre_topc @ X23)))),
% 0.41/0.60      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      ((![X20 : $i, X21 : $i]:
% 0.41/0.60          (~ (l1_pre_topc @ X20)
% 0.41/0.60           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.41/0.60           | ~ (v3_pre_topc @ X21 @ X20)
% 0.41/0.60           | ((k1_tops_1 @ X20 @ X21) = (X21)))) | 
% 0.41/0.60       (![X22 : $i, X23 : $i]:
% 0.41/0.60          (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.41/0.60           | ~ (l1_pre_topc @ X23)
% 0.41/0.60           | ~ (v2_pre_topc @ X23)))),
% 0.41/0.60      inference('split', [status(esa)], ['6'])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      ((![X20 : $i, X21 : $i]:
% 0.41/0.60          (~ (l1_pre_topc @ X20)
% 0.41/0.60           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.41/0.60           | ~ (v3_pre_topc @ X21 @ X20)
% 0.41/0.60           | ((k1_tops_1 @ X20 @ X21) = (X21))))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X20 : $i, X21 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X20)
% 0.41/0.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.41/0.60          | ~ (v3_pre_topc @ X21 @ X20)
% 0.41/0.60          | ((k1_tops_1 @ X20 @ X21) = (X21)))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['7', '15'])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.41/0.60        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['5', '16'])).
% 0.41/0.60  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.41/0.60         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['4', '19'])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(l78_tops_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( ( k2_tops_1 @ A @ B ) =
% 0.41/0.60             ( k7_subset_1 @
% 0.41/0.60               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.41/0.60               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.41/0.60          | ((k2_tops_1 @ X19 @ X18)
% 0.41/0.60              = (k7_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.41/0.60                 (k2_pre_topc @ X19 @ X18) @ (k1_tops_1 @ X19 @ X18)))
% 0.41/0.60          | ~ (l1_pre_topc @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(dt_k2_pre_topc, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( l1_pre_topc @ A ) & 
% 0.41/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.60       ( m1_subset_1 @
% 0.41/0.60         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X12 : $i, X13 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X12)
% 0.41/0.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.41/0.60          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 0.41/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.41/0.60  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['27', '28'])).
% 0.41/0.60  thf(redefinition_k7_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.41/0.60          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.60           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.60            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['23', '24', '31'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.41/0.60         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['20', '32'])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.60           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.41/0.60             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['33', '36'])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.41/0.60       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.41/0.60      inference('simplify', [status(thm)], ['37'])).
% 0.41/0.60  thf('39', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['2', '38'])).
% 0.41/0.60  thf('40', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X20)
% 0.41/0.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.41/0.60          | ((k1_tops_1 @ X23 @ X22) != (X22))
% 0.41/0.60          | (v3_pre_topc @ X22 @ X23)
% 0.41/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.41/0.60          | ~ (l1_pre_topc @ X23)
% 0.41/0.60          | ~ (v2_pre_topc @ X23))),
% 0.41/0.60      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      ((![X22 : $i, X23 : $i]:
% 0.41/0.60          (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.41/0.60           | ~ (l1_pre_topc @ X23)
% 0.41/0.60           | ~ (v2_pre_topc @ X23)
% 0.41/0.60           | ((k1_tops_1 @ X23 @ X22) != (X22))
% 0.41/0.60           | (v3_pre_topc @ X22 @ X23)))
% 0.41/0.60         <= ((![X22 : $i, X23 : $i]:
% 0.41/0.60                (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.41/0.60                 | ~ (l1_pre_topc @ X23)
% 0.41/0.60                 | ~ (v2_pre_topc @ X23)
% 0.41/0.60                 | ((k1_tops_1 @ X23 @ X22) != (X22))
% 0.41/0.60                 | (v3_pre_topc @ X22 @ X23))))),
% 0.41/0.60      inference('split', [status(esa)], ['42'])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      ((![X20 : $i, X21 : $i]:
% 0.41/0.60          (~ (l1_pre_topc @ X20)
% 0.41/0.60           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))))
% 0.41/0.60         <= ((![X20 : $i, X21 : $i]:
% 0.41/0.60                (~ (l1_pre_topc @ X20)
% 0.41/0.60                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))))),
% 0.41/0.60      inference('split', [status(esa)], ['42'])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A))
% 0.41/0.60         <= ((![X20 : $i, X21 : $i]:
% 0.41/0.60                (~ (l1_pre_topc @ X20)
% 0.41/0.60                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.60  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      (~
% 0.41/0.60       (![X20 : $i, X21 : $i]:
% 0.41/0.60          (~ (l1_pre_topc @ X20)
% 0.41/0.60           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))))),
% 0.41/0.60      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      ((![X22 : $i, X23 : $i]:
% 0.41/0.60          (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.41/0.60           | ~ (l1_pre_topc @ X23)
% 0.41/0.60           | ~ (v2_pre_topc @ X23)
% 0.41/0.60           | ((k1_tops_1 @ X23 @ X22) != (X22))
% 0.41/0.60           | (v3_pre_topc @ X22 @ X23))) | 
% 0.41/0.60       (![X20 : $i, X21 : $i]:
% 0.41/0.60          (~ (l1_pre_topc @ X20)
% 0.41/0.60           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))))),
% 0.41/0.60      inference('split', [status(esa)], ['42'])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      ((![X22 : $i, X23 : $i]:
% 0.41/0.60          (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.41/0.60           | ~ (l1_pre_topc @ X23)
% 0.41/0.60           | ~ (v2_pre_topc @ X23)
% 0.41/0.60           | ((k1_tops_1 @ X23 @ X22) != (X22))
% 0.41/0.60           | (v3_pre_topc @ X22 @ X23)))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (![X22 : $i, X23 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.41/0.60          | ~ (l1_pre_topc @ X23)
% 0.41/0.60          | ~ (v2_pre_topc @ X23)
% 0.41/0.60          | ((k1_tops_1 @ X23 @ X22) != (X22))
% 0.41/0.60          | (v3_pre_topc @ X22 @ X23))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['43', '50'])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      (((v3_pre_topc @ sk_B @ sk_A)
% 0.41/0.60        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 0.41/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['41', '51'])).
% 0.41/0.60  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('55', plain,
% 0.41/0.60      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t74_tops_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( ( k1_tops_1 @ A @ B ) =
% 0.41/0.60             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.60  thf('57', plain,
% 0.41/0.60      (![X26 : $i, X27 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.41/0.60          | ((k1_tops_1 @ X27 @ X26)
% 0.41/0.60              = (k7_subset_1 @ (u1_struct_0 @ X27) @ X26 @ 
% 0.41/0.60                 (k2_tops_1 @ X27 @ X26)))
% 0.41/0.60          | ~ (l1_pre_topc @ X27))),
% 0.41/0.60      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.41/0.60  thf('58', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.41/0.60            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.60               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['56', '57'])).
% 0.41/0.60  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('60', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('61', plain,
% 0.41/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.41/0.60          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.41/0.60  thf('62', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.41/0.60           = (k4_xboole_0 @ sk_B @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.41/0.60  thf('63', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.60           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.60  thf('64', plain,
% 0.41/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.41/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('65', plain,
% 0.41/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.41/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.41/0.60      inference('sup+', [status(thm)], ['63', '64'])).
% 0.41/0.60  thf('66', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t48_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.41/0.60  thf('67', plain,
% 0.41/0.60      (![X14 : $i, X15 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.41/0.60          | (r1_tarski @ X14 @ (k2_pre_topc @ X15 @ X14))
% 0.41/0.60          | ~ (l1_pre_topc @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.41/0.60  thf('68', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['66', '67'])).
% 0.41/0.60  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('70', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['68', '69'])).
% 0.41/0.60  thf(t28_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.60  thf('71', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i]:
% 0.41/0.60         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.60  thf('72', plain,
% 0.41/0.60      (((k3_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['70', '71'])).
% 0.41/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.41/0.60  thf('73', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.60  thf(t89_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ))).
% 0.41/0.60  thf('74', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i]:
% 0.41/0.60         (r1_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k4_xboole_0 @ X7 @ X8))),
% 0.41/0.60      inference('cnf', [status(esa)], [t89_xboole_1])).
% 0.41/0.60  thf('75', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['73', '74'])).
% 0.41/0.60  thf(t83_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.60  thf('76', plain,
% 0.41/0.60      (![X4 : $i, X5 : $i]:
% 0.41/0.60         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.41/0.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.60  thf('77', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.41/0.60           = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['75', '76'])).
% 0.41/0.60  thf('78', plain,
% 0.41/0.60      (((k4_xboole_0 @ sk_B @ 
% 0.41/0.60         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.41/0.60         = (k3_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['72', '77'])).
% 0.41/0.60  thf('79', plain,
% 0.41/0.60      (((k3_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['70', '71'])).
% 0.41/0.60  thf('80', plain,
% 0.41/0.60      (((k4_xboole_0 @ sk_B @ 
% 0.41/0.60         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['78', '79'])).
% 0.41/0.60  thf('81', plain,
% 0.41/0.60      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.41/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.41/0.60      inference('sup+', [status(thm)], ['65', '80'])).
% 0.41/0.60  thf('82', plain,
% 0.41/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.41/0.60       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('83', plain,
% 0.41/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['2', '38', '82'])).
% 0.41/0.60  thf('84', plain,
% 0.41/0.60      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['81', '83'])).
% 0.41/0.60  thf('85', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['58', '59', '62', '84'])).
% 0.41/0.60  thf('86', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['55', '85'])).
% 0.41/0.60  thf('87', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.41/0.60      inference('simplify', [status(thm)], ['86'])).
% 0.41/0.60  thf('88', plain, ($false), inference('demod', [status(thm)], ['40', '87'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
