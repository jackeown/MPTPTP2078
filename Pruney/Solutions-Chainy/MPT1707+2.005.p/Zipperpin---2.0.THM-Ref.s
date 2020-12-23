%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iVzRPUAEpm

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:11 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 617 expanded)
%              Number of leaves         :   24 ( 175 expanded)
%              Depth                    :   37
%              Number of atoms          : 1439 (13248 expanded)
%              Number of equality atoms :   45 ( 549 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t16_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) )
                 => ~ ( ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                         => ( E != D ) )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) )
                         => ( E != D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) )
                   => ~ ( ! [E: $i] :
                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                           => ( E != D ) )
                        & ! [E: $i] :
                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) )
                           => ( E != D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X18 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X18 @ X17 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(d2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_pre_topc @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( D
                      = ( k1_tsep_1 @ A @ B @ C ) )
                  <=> ( ( u1_struct_0 @ D )
                      = ( k2_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( v1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( X15
       != ( k1_tsep_1 @ X14 @ X13 @ X16 ) )
      | ( ( u1_struct_0 @ X15 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('16',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X13 @ X16 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X14 @ X13 @ X16 ) @ X14 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X14 @ X13 @ X16 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X14 @ X13 @ X16 ) )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['7','22'])).

thf('24',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X18 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('35',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('36',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X5
       != ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('41',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['34','42'])).

thf('44',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('45',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('46',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('47',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k2_xboole_0 @ X6 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X20: $i] :
      ( ( X20 != sk_D_1 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    ! [X21: $i] :
      ( ( X21 != sk_D_1 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('63',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('64',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('65',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X6 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('66',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k2_xboole_0 @ X6 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X6 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['62','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X4: $i,X6: $i,X8: $i] :
      ( ( X8
        = ( k2_xboole_0 @ X6 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X4 @ X6 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X4 @ X6 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X8 @ X4 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['79'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['81'])).

thf('83',plain,(
    ! [X4: $i,X6: $i,X8: $i] :
      ( ( X8
        = ( k2_xboole_0 @ X6 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X4 @ X6 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X4 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['81'])).

thf('87',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['80','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X1 ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( u1_struct_0 @ sk_B_1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['78','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ sk_B_1 )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','93'])).

thf('95',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ sk_B_1 )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('103',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','101','102'])).

thf('104',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['0','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iVzRPUAEpm
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:07:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.70/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.88  % Solved by: fo/fo7.sh
% 0.70/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.88  % done 599 iterations in 0.429s
% 0.70/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.88  % SZS output start Refutation
% 0.70/0.88  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.70/0.88  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.70/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.70/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.88  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.70/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.70/0.88  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.70/0.88  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.70/0.88  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.70/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.70/0.88  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.70/0.88  thf(sk_B_type, type, sk_B: $i > $i).
% 0.70/0.88  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.70/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.88  thf(t16_tmap_1, conjecture,
% 0.70/0.88    (![A:$i]:
% 0.70/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.88       ( ![B:$i]:
% 0.70/0.88         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.70/0.88           ( ![C:$i]:
% 0.70/0.88             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.70/0.88               ( ![D:$i]:
% 0.70/0.88                 ( ( m1_subset_1 @
% 0.70/0.88                     D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 0.70/0.88                   ( ~( ( ![E:$i]:
% 0.70/0.88                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.70/0.88                            ( ( E ) != ( D ) ) ) ) & 
% 0.70/0.88                        ( ![E:$i]:
% 0.70/0.88                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 0.70/0.88                            ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.70/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.88    (~( ![A:$i]:
% 0.70/0.88        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.70/0.88            ( l1_pre_topc @ A ) ) =>
% 0.70/0.88          ( ![B:$i]:
% 0.70/0.88            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.70/0.88              ( ![C:$i]:
% 0.70/0.88                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.70/0.88                  ( ![D:$i]:
% 0.70/0.88                    ( ( m1_subset_1 @
% 0.70/0.88                        D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 0.70/0.88                      ( ~( ( ![E:$i]:
% 0.70/0.88                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.70/0.88                               ( ( E ) != ( D ) ) ) ) & 
% 0.70/0.88                           ( ![E:$i]:
% 0.70/0.88                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 0.70/0.88                               ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.70/0.88    inference('cnf.neg', [status(esa)], [t16_tmap_1])).
% 0.70/0.88  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('2', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(dt_k1_tsep_1, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.70/0.88         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 0.70/0.88         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.70/0.88       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 0.70/0.88         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 0.70/0.88         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 0.70/0.88  thf('3', plain,
% 0.70/0.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.70/0.88         (~ (m1_pre_topc @ X17 @ X18)
% 0.70/0.88          | (v2_struct_0 @ X17)
% 0.70/0.88          | ~ (l1_pre_topc @ X18)
% 0.70/0.88          | (v2_struct_0 @ X18)
% 0.70/0.88          | (v2_struct_0 @ X19)
% 0.70/0.88          | ~ (m1_pre_topc @ X19 @ X18)
% 0.70/0.88          | (v1_pre_topc @ (k1_tsep_1 @ X18 @ X17 @ X19)))),
% 0.70/0.88      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.70/0.88  thf('4', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ X0))
% 0.70/0.88          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.70/0.88          | (v2_struct_0 @ X0)
% 0.70/0.88          | (v2_struct_0 @ sk_A)
% 0.70/0.88          | ~ (l1_pre_topc @ sk_A)
% 0.70/0.88          | (v2_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['2', '3'])).
% 0.70/0.88  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('6', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ X0))
% 0.70/0.88          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.70/0.88          | (v2_struct_0 @ X0)
% 0.70/0.88          | (v2_struct_0 @ sk_A)
% 0.70/0.88          | (v2_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('demod', [status(thm)], ['4', '5'])).
% 0.70/0.88  thf('7', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['1', '6'])).
% 0.70/0.88  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('9', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('10', plain,
% 0.70/0.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.70/0.88         (~ (m1_pre_topc @ X17 @ X18)
% 0.70/0.88          | (v2_struct_0 @ X17)
% 0.70/0.88          | ~ (l1_pre_topc @ X18)
% 0.70/0.88          | (v2_struct_0 @ X18)
% 0.70/0.88          | (v2_struct_0 @ X19)
% 0.70/0.88          | ~ (m1_pre_topc @ X19 @ X18)
% 0.70/0.88          | (m1_pre_topc @ (k1_tsep_1 @ X18 @ X17 @ X19) @ X18))),
% 0.70/0.88      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.70/0.88  thf('11', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ X0) @ sk_A)
% 0.70/0.88          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.70/0.88          | (v2_struct_0 @ X0)
% 0.70/0.88          | (v2_struct_0 @ sk_A)
% 0.70/0.88          | ~ (l1_pre_topc @ sk_A)
% 0.70/0.88          | (v2_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['9', '10'])).
% 0.70/0.88  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('13', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ X0) @ sk_A)
% 0.70/0.88          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.70/0.88          | (v2_struct_0 @ X0)
% 0.70/0.88          | (v2_struct_0 @ sk_A)
% 0.70/0.88          | (v2_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('demod', [status(thm)], ['11', '12'])).
% 0.70/0.88  thf('14', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C) @ sk_A))),
% 0.70/0.88      inference('sup-', [status(thm)], ['8', '13'])).
% 0.70/0.88  thf(d2_tsep_1, axiom,
% 0.70/0.88    (![A:$i]:
% 0.70/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.88       ( ![B:$i]:
% 0.70/0.88         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.70/0.88           ( ![C:$i]:
% 0.70/0.88             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.70/0.88               ( ![D:$i]:
% 0.70/0.88                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.70/0.88                     ( m1_pre_topc @ D @ A ) ) =>
% 0.70/0.88                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 0.70/0.88                     ( ( u1_struct_0 @ D ) =
% 0.70/0.88                       ( k2_xboole_0 @
% 0.70/0.88                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.70/0.88  thf('15', plain,
% 0.70/0.88      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.70/0.88         ((v2_struct_0 @ X13)
% 0.70/0.88          | ~ (m1_pre_topc @ X13 @ X14)
% 0.70/0.88          | (v2_struct_0 @ X15)
% 0.70/0.88          | ~ (v1_pre_topc @ X15)
% 0.70/0.88          | ~ (m1_pre_topc @ X15 @ X14)
% 0.70/0.88          | ((X15) != (k1_tsep_1 @ X14 @ X13 @ X16))
% 0.70/0.88          | ((u1_struct_0 @ X15)
% 0.70/0.88              = (k2_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))
% 0.70/0.88          | ~ (m1_pre_topc @ X16 @ X14)
% 0.70/0.88          | (v2_struct_0 @ X16)
% 0.70/0.88          | ~ (l1_pre_topc @ X14)
% 0.70/0.88          | (v2_struct_0 @ X14))),
% 0.70/0.88      inference('cnf', [status(esa)], [d2_tsep_1])).
% 0.70/0.88  thf('16', plain,
% 0.70/0.88      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.70/0.88         ((v2_struct_0 @ X14)
% 0.70/0.88          | ~ (l1_pre_topc @ X14)
% 0.70/0.88          | (v2_struct_0 @ X16)
% 0.70/0.88          | ~ (m1_pre_topc @ X16 @ X14)
% 0.70/0.88          | ((u1_struct_0 @ (k1_tsep_1 @ X14 @ X13 @ X16))
% 0.70/0.88              = (k2_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))
% 0.70/0.88          | ~ (m1_pre_topc @ (k1_tsep_1 @ X14 @ X13 @ X16) @ X14)
% 0.70/0.88          | ~ (v1_pre_topc @ (k1_tsep_1 @ X14 @ X13 @ X16))
% 0.70/0.88          | (v2_struct_0 @ (k1_tsep_1 @ X14 @ X13 @ X16))
% 0.70/0.88          | ~ (m1_pre_topc @ X13 @ X14)
% 0.70/0.88          | (v2_struct_0 @ X13))),
% 0.70/0.88      inference('simplify', [status(thm)], ['15'])).
% 0.70/0.88  thf('17', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.70/0.88        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_A))),
% 0.70/0.88      inference('sup-', [status(thm)], ['14', '16'])).
% 0.70/0.88  thf('18', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('21', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A))),
% 0.70/0.88      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.70/0.88  thf('22', plain,
% 0.70/0.88      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88          = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.70/0.88        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C))),
% 0.70/0.88      inference('simplify', [status(thm)], ['21'])).
% 0.70/0.88  thf('23', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))),
% 0.70/0.88      inference('sup-', [status(thm)], ['7', '22'])).
% 0.70/0.88  thf('24', plain,
% 0.70/0.88      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88          = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.70/0.88        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C))),
% 0.70/0.88      inference('simplify', [status(thm)], ['23'])).
% 0.70/0.88  thf('25', plain,
% 0.70/0.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.70/0.88         (~ (m1_pre_topc @ X17 @ X18)
% 0.70/0.88          | (v2_struct_0 @ X17)
% 0.70/0.88          | ~ (l1_pre_topc @ X18)
% 0.70/0.88          | (v2_struct_0 @ X18)
% 0.70/0.88          | (v2_struct_0 @ X19)
% 0.70/0.88          | ~ (m1_pre_topc @ X19 @ X18)
% 0.70/0.88          | ~ (v2_struct_0 @ (k1_tsep_1 @ X18 @ X17 @ X19)))),
% 0.70/0.88      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.70/0.88  thf('26', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.70/0.88        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | ~ (m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.70/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.70/0.88  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('29', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('30', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.70/0.88  thf('31', plain,
% 0.70/0.88      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88          = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C))),
% 0.70/0.88      inference('simplify', [status(thm)], ['30'])).
% 0.70/0.88  thf('32', plain,
% 0.70/0.88      ((m1_subset_1 @ sk_D_1 @ 
% 0.70/0.88        (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('33', plain,
% 0.70/0.88      (((m1_subset_1 @ sk_D_1 @ 
% 0.70/0.88         (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('sup+', [status(thm)], ['31', '32'])).
% 0.70/0.88  thf('34', plain,
% 0.70/0.88      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88          = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C))),
% 0.70/0.88      inference('simplify', [status(thm)], ['30'])).
% 0.70/0.88  thf('35', plain,
% 0.70/0.88      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.70/0.88          = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C))),
% 0.70/0.88      inference('simplify', [status(thm)], ['30'])).
% 0.70/0.88  thf('36', plain,
% 0.70/0.88      ((m1_subset_1 @ sk_D_1 @ 
% 0.70/0.88        (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(t2_subset, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( m1_subset_1 @ A @ B ) =>
% 0.70/0.88       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.70/0.88  thf('37', plain,
% 0.70/0.88      (![X11 : $i, X12 : $i]:
% 0.70/0.88         ((r2_hidden @ X11 @ X12)
% 0.70/0.88          | (v1_xboole_0 @ X12)
% 0.70/0.88          | ~ (m1_subset_1 @ X11 @ X12))),
% 0.70/0.88      inference('cnf', [status(esa)], [t2_subset])).
% 0.70/0.88  thf('38', plain,
% 0.70/0.88      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ 
% 0.70/0.88           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))))),
% 0.70/0.88      inference('sup-', [status(thm)], ['36', '37'])).
% 0.70/0.88  thf('39', plain,
% 0.70/0.88      (((r2_hidden @ sk_D_1 @ 
% 0.70/0.88         (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))))),
% 0.70/0.88      inference('sup+', [status(thm)], ['35', '38'])).
% 0.70/0.88  thf(d3_xboole_0, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.70/0.88       ( ![D:$i]:
% 0.70/0.88         ( ( r2_hidden @ D @ C ) <=>
% 0.70/0.88           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.70/0.88  thf('40', plain,
% 0.70/0.88      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X7 @ X5)
% 0.70/0.88          | (r2_hidden @ X7 @ X6)
% 0.70/0.88          | (r2_hidden @ X7 @ X4)
% 0.70/0.88          | ((X5) != (k2_xboole_0 @ X6 @ X4)))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.70/0.88  thf('41', plain,
% 0.70/0.88      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.70/0.88         ((r2_hidden @ X7 @ X4)
% 0.70/0.88          | (r2_hidden @ X7 @ X6)
% 0.70/0.88          | ~ (r2_hidden @ X7 @ (k2_xboole_0 @ X6 @ X4)))),
% 0.70/0.88      inference('simplify', [status(thm)], ['40'])).
% 0.70/0.88  thf('42', plain,
% 0.70/0.88      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['39', '41'])).
% 0.70/0.88  thf('43', plain,
% 0.70/0.88      (((v1_xboole_0 @ 
% 0.70/0.88         (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('sup+', [status(thm)], ['34', '42'])).
% 0.70/0.88  thf('44', plain,
% 0.70/0.88      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v1_xboole_0 @ 
% 0.70/0.88           (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))),
% 0.70/0.88      inference('simplify', [status(thm)], ['43'])).
% 0.70/0.88  thf(d1_xboole_0, axiom,
% 0.70/0.88    (![A:$i]:
% 0.70/0.88     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.70/0.88  thf('45', plain,
% 0.70/0.88      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.70/0.88      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.88  thf('46', plain,
% 0.70/0.88      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X3 @ X4)
% 0.70/0.88          | (r2_hidden @ X3 @ X5)
% 0.70/0.88          | ((X5) != (k2_xboole_0 @ X6 @ X4)))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.70/0.88  thf('47', plain,
% 0.70/0.88      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.70/0.88         ((r2_hidden @ X3 @ (k2_xboole_0 @ X6 @ X4)) | ~ (r2_hidden @ X3 @ X4))),
% 0.70/0.88      inference('simplify', [status(thm)], ['46'])).
% 0.70/0.88  thf('48', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((v1_xboole_0 @ X0)
% 0.70/0.88          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['45', '47'])).
% 0.70/0.88  thf('49', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.70/0.88      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.88  thf('50', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['48', '49'])).
% 0.70/0.88  thf('51', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['44', '50'])).
% 0.70/0.88  thf(t1_subset, axiom,
% 0.70/0.88    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.70/0.88  thf('52', plain,
% 0.70/0.88      (![X9 : $i, X10 : $i]:
% 0.70/0.88         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.70/0.88      inference('cnf', [status(esa)], [t1_subset])).
% 0.70/0.88  thf('53', plain,
% 0.70/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['51', '52'])).
% 0.70/0.88  thf('54', plain,
% 0.70/0.88      (![X9 : $i, X10 : $i]:
% 0.70/0.88         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.70/0.88      inference('cnf', [status(esa)], [t1_subset])).
% 0.70/0.88  thf('55', plain,
% 0.70/0.88      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.70/0.88        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['53', '54'])).
% 0.70/0.88  thf('56', plain,
% 0.70/0.88      (![X20 : $i]:
% 0.70/0.88         (((X20) != (sk_D_1)) | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_C)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('57', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 0.70/0.88      inference('simplify', [status(thm)], ['56'])).
% 0.70/0.88  thf('58', plain,
% 0.70/0.88      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C))),
% 0.70/0.88      inference('sup-', [status(thm)], ['55', '57'])).
% 0.70/0.88  thf('59', plain,
% 0.70/0.88      (![X21 : $i]:
% 0.70/0.88         (((X21) != (sk_D_1)) | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_B_1)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('60', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('simplify', [status(thm)], ['59'])).
% 0.70/0.88  thf('61', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['58', '60'])).
% 0.70/0.88  thf('62', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['58', '60'])).
% 0.70/0.88  thf('63', plain,
% 0.70/0.88      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v1_xboole_0 @ 
% 0.70/0.88           (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))),
% 0.70/0.88      inference('simplify', [status(thm)], ['43'])).
% 0.70/0.88  thf('64', plain,
% 0.70/0.88      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.70/0.88      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.88  thf('65', plain,
% 0.70/0.88      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X3 @ X6)
% 0.70/0.88          | (r2_hidden @ X3 @ X5)
% 0.70/0.88          | ((X5) != (k2_xboole_0 @ X6 @ X4)))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.70/0.88  thf('66', plain,
% 0.70/0.88      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.70/0.88         ((r2_hidden @ X3 @ (k2_xboole_0 @ X6 @ X4)) | ~ (r2_hidden @ X3 @ X6))),
% 0.70/0.88      inference('simplify', [status(thm)], ['65'])).
% 0.70/0.88  thf('67', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((v1_xboole_0 @ X0)
% 0.70/0.88          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['64', '66'])).
% 0.70/0.88  thf('68', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.70/0.88      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.88  thf('69', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['67', '68'])).
% 0.70/0.88  thf('70', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['63', '69'])).
% 0.70/0.88  thf('71', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.70/0.88      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.88  thf('72', plain,
% 0.70/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['70', '71'])).
% 0.70/0.88  thf('73', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['62', '72'])).
% 0.70/0.88  thf('74', plain,
% 0.70/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('simplify', [status(thm)], ['73'])).
% 0.70/0.88  thf('75', plain,
% 0.70/0.88      (![X9 : $i, X10 : $i]:
% 0.70/0.88         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.70/0.88      inference('cnf', [status(esa)], [t1_subset])).
% 0.70/0.88  thf('76', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['74', '75'])).
% 0.70/0.88  thf('77', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('simplify', [status(thm)], ['59'])).
% 0.70/0.88  thf('78', plain,
% 0.70/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['76', '77'])).
% 0.70/0.88  thf('79', plain,
% 0.70/0.88      (![X4 : $i, X6 : $i, X8 : $i]:
% 0.70/0.88         (((X8) = (k2_xboole_0 @ X6 @ X4))
% 0.70/0.88          | (r2_hidden @ (sk_D @ X8 @ X4 @ X6) @ X4)
% 0.70/0.88          | (r2_hidden @ (sk_D @ X8 @ X4 @ X6) @ X6)
% 0.70/0.88          | (r2_hidden @ (sk_D @ X8 @ X4 @ X6) @ X8))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.70/0.88  thf('80', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.70/0.88          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 0.70/0.88          | ((X1) = (k2_xboole_0 @ X0 @ X0)))),
% 0.70/0.88      inference('eq_fact', [status(thm)], ['79'])).
% 0.70/0.88  thf('81', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.70/0.88          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 0.70/0.88          | ((X1) = (k2_xboole_0 @ X0 @ X0)))),
% 0.70/0.88      inference('eq_fact', [status(thm)], ['79'])).
% 0.70/0.88  thf('82', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 0.70/0.88          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 0.70/0.88      inference('eq_fact', [status(thm)], ['81'])).
% 0.70/0.88  thf('83', plain,
% 0.70/0.88      (![X4 : $i, X6 : $i, X8 : $i]:
% 0.70/0.88         (((X8) = (k2_xboole_0 @ X6 @ X4))
% 0.70/0.88          | ~ (r2_hidden @ (sk_D @ X8 @ X4 @ X6) @ X4)
% 0.70/0.88          | ~ (r2_hidden @ (sk_D @ X8 @ X4 @ X6) @ X8))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.70/0.88  thf('84', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 0.70/0.88          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.70/0.88          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['82', '83'])).
% 0.70/0.88  thf('85', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.70/0.88          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 0.70/0.88      inference('simplify', [status(thm)], ['84'])).
% 0.70/0.88  thf('86', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 0.70/0.88          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 0.70/0.88      inference('eq_fact', [status(thm)], ['81'])).
% 0.70/0.88  thf('87', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.70/0.88      inference('clc', [status(thm)], ['85', '86'])).
% 0.70/0.88  thf('88', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.70/0.88          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 0.70/0.88          | ((X1) = (X0)))),
% 0.70/0.88      inference('demod', [status(thm)], ['80', '87'])).
% 0.70/0.88  thf('89', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.70/0.88      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.88  thf('90', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         (((X0) = (X1))
% 0.70/0.88          | (r2_hidden @ (sk_D @ X0 @ X1 @ X1) @ X1)
% 0.70/0.88          | ~ (v1_xboole_0 @ X0))),
% 0.70/0.88      inference('sup-', [status(thm)], ['88', '89'])).
% 0.70/0.88  thf('91', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.70/0.88      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.88  thf('92', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.88      inference('sup-', [status(thm)], ['90', '91'])).
% 0.70/0.88  thf('93', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((v2_struct_0 @ sk_B_1)
% 0.70/0.88          | (v2_struct_0 @ sk_A)
% 0.70/0.88          | (v2_struct_0 @ sk_C)
% 0.70/0.88          | ~ (v1_xboole_0 @ X0)
% 0.70/0.88          | ((u1_struct_0 @ sk_B_1) = (X0)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['78', '92'])).
% 0.70/0.88  thf('94', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | ((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_C))
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['61', '93'])).
% 0.70/0.88  thf('95', plain,
% 0.70/0.88      ((((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_C))
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('simplify', [status(thm)], ['94'])).
% 0.70/0.88  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('97', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_B_1)
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | ((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_C)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['95', '96'])).
% 0.70/0.88  thf('98', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('99', plain,
% 0.70/0.88      ((((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_C)) | (v2_struct_0 @ sk_C))),
% 0.70/0.88      inference('clc', [status(thm)], ['97', '98'])).
% 0.70/0.88  thf('100', plain, (~ (v2_struct_0 @ sk_C)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('101', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_C))),
% 0.70/0.88      inference('clc', [status(thm)], ['99', '100'])).
% 0.70/0.88  thf('102', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.70/0.88      inference('clc', [status(thm)], ['85', '86'])).
% 0.70/0.88  thf('103', plain,
% 0.70/0.88      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.70/0.88        | (v2_struct_0 @ sk_C)
% 0.70/0.88        | (v2_struct_0 @ sk_A)
% 0.70/0.88        | (v2_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('demod', [status(thm)], ['33', '101', '102'])).
% 0.70/0.88  thf('104', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1))),
% 0.70/0.88      inference('simplify', [status(thm)], ['59'])).
% 0.70/0.88  thf('105', plain,
% 0.70/0.88      (((v2_struct_0 @ sk_B_1) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.70/0.88      inference('sup-', [status(thm)], ['103', '104'])).
% 0.70/0.88  thf('106', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('107', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.70/0.88      inference('clc', [status(thm)], ['105', '106'])).
% 0.70/0.88  thf('108', plain, (~ (v2_struct_0 @ sk_C)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('109', plain, ((v2_struct_0 @ sk_A)),
% 0.70/0.88      inference('clc', [status(thm)], ['107', '108'])).
% 0.70/0.88  thf('110', plain, ($false), inference('demod', [status(thm)], ['0', '109'])).
% 0.70/0.88  
% 0.70/0.88  % SZS output end Refutation
% 0.70/0.88  
% 0.70/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
