%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EwXVkkrfuC

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:12 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 291 expanded)
%              Number of leaves         :   22 (  88 expanded)
%              Depth                    :   28
%              Number of atoms          : 1107 (6142 expanded)
%              Number of equality atoms :   22 ( 248 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_pre_topc @ sk_B @ sk_A ),
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
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
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
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
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
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
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
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['7','22'])).

thf('24',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
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
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('37',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('38',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(fc5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_xboole_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X20: $i] :
      ( ( X20 != sk_D_1 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X21: $i] :
      ( ( X21 != sk_D_1 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ( m1_subset_1 @ X10 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('55',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('56',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('58',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X10 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('60',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['56','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['0','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EwXVkkrfuC
% 0.14/0.33  % Computer   : n025.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:12:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 1.76/1.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.76/1.95  % Solved by: fo/fo7.sh
% 1.76/1.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.76/1.95  % done 1418 iterations in 1.521s
% 1.76/1.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.76/1.95  % SZS output start Refutation
% 1.76/1.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.76/1.95  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 1.76/1.95  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.76/1.95  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.76/1.95  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.76/1.95  thf(sk_B_type, type, sk_B: $i).
% 1.76/1.95  thf(sk_C_type, type, sk_C: $i).
% 1.76/1.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.76/1.95  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.76/1.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.76/1.95  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.76/1.95  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.76/1.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.76/1.95  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.76/1.95  thf(sk_A_type, type, sk_A: $i).
% 1.76/1.95  thf(t16_tmap_1, conjecture,
% 1.76/1.95    (![A:$i]:
% 1.76/1.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.76/1.95       ( ![B:$i]:
% 1.76/1.95         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.76/1.95           ( ![C:$i]:
% 1.76/1.95             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.76/1.95               ( ![D:$i]:
% 1.76/1.95                 ( ( m1_subset_1 @
% 1.76/1.95                     D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 1.76/1.95                   ( ~( ( ![E:$i]:
% 1.76/1.95                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.76/1.95                            ( ( E ) != ( D ) ) ) ) & 
% 1.76/1.95                        ( ![E:$i]:
% 1.76/1.95                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 1.76/1.95                            ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.76/1.95  thf(zf_stmt_0, negated_conjecture,
% 1.76/1.95    (~( ![A:$i]:
% 1.76/1.95        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.76/1.95            ( l1_pre_topc @ A ) ) =>
% 1.76/1.95          ( ![B:$i]:
% 1.76/1.95            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.76/1.95              ( ![C:$i]:
% 1.76/1.95                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.76/1.95                  ( ![D:$i]:
% 1.76/1.95                    ( ( m1_subset_1 @
% 1.76/1.95                        D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 1.76/1.95                      ( ~( ( ![E:$i]:
% 1.76/1.95                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.76/1.95                               ( ( E ) != ( D ) ) ) ) & 
% 1.76/1.95                           ( ![E:$i]:
% 1.76/1.95                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 1.76/1.95                               ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.76/1.95    inference('cnf.neg', [status(esa)], [t16_tmap_1])).
% 1.76/1.95  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf(dt_k1_tsep_1, axiom,
% 1.76/1.95    (![A:$i,B:$i,C:$i]:
% 1.76/1.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.76/1.95         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 1.76/1.95         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.76/1.95       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 1.76/1.95         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 1.76/1.95         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 1.76/1.95  thf('3', plain,
% 1.76/1.95      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.76/1.95         (~ (m1_pre_topc @ X17 @ X18)
% 1.76/1.95          | (v2_struct_0 @ X17)
% 1.76/1.95          | ~ (l1_pre_topc @ X18)
% 1.76/1.95          | (v2_struct_0 @ X18)
% 1.76/1.95          | (v2_struct_0 @ X19)
% 1.76/1.95          | ~ (m1_pre_topc @ X19 @ X18)
% 1.76/1.95          | (v1_pre_topc @ (k1_tsep_1 @ X18 @ X17 @ X19)))),
% 1.76/1.95      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.76/1.95  thf('4', plain,
% 1.76/1.95      (![X0 : $i]:
% 1.76/1.95         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.76/1.95          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.76/1.95          | (v2_struct_0 @ X0)
% 1.76/1.95          | (v2_struct_0 @ sk_A)
% 1.76/1.95          | ~ (l1_pre_topc @ sk_A)
% 1.76/1.95          | (v2_struct_0 @ sk_B))),
% 1.76/1.95      inference('sup-', [status(thm)], ['2', '3'])).
% 1.76/1.95  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('6', plain,
% 1.76/1.95      (![X0 : $i]:
% 1.76/1.95         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.76/1.95          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.76/1.95          | (v2_struct_0 @ X0)
% 1.76/1.95          | (v2_struct_0 @ sk_A)
% 1.76/1.95          | (v2_struct_0 @ sk_B))),
% 1.76/1.95      inference('demod', [status(thm)], ['4', '5'])).
% 1.76/1.95  thf('7', plain,
% 1.76/1.95      (((v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['1', '6'])).
% 1.76/1.95  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('10', plain,
% 1.76/1.95      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.76/1.95         (~ (m1_pre_topc @ X17 @ X18)
% 1.76/1.95          | (v2_struct_0 @ X17)
% 1.76/1.95          | ~ (l1_pre_topc @ X18)
% 1.76/1.95          | (v2_struct_0 @ X18)
% 1.76/1.95          | (v2_struct_0 @ X19)
% 1.76/1.95          | ~ (m1_pre_topc @ X19 @ X18)
% 1.76/1.95          | (m1_pre_topc @ (k1_tsep_1 @ X18 @ X17 @ X19) @ X18))),
% 1.76/1.95      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.76/1.95  thf('11', plain,
% 1.76/1.95      (![X0 : $i]:
% 1.76/1.95         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.76/1.95          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.76/1.95          | (v2_struct_0 @ X0)
% 1.76/1.95          | (v2_struct_0 @ sk_A)
% 1.76/1.95          | ~ (l1_pre_topc @ sk_A)
% 1.76/1.95          | (v2_struct_0 @ sk_B))),
% 1.76/1.95      inference('sup-', [status(thm)], ['9', '10'])).
% 1.76/1.95  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('13', plain,
% 1.76/1.95      (![X0 : $i]:
% 1.76/1.95         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.76/1.95          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.76/1.95          | (v2_struct_0 @ X0)
% 1.76/1.95          | (v2_struct_0 @ sk_A)
% 1.76/1.95          | (v2_struct_0 @ sk_B))),
% 1.76/1.95      inference('demod', [status(thm)], ['11', '12'])).
% 1.76/1.95  thf('14', plain,
% 1.76/1.95      (((v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.76/1.95      inference('sup-', [status(thm)], ['8', '13'])).
% 1.76/1.95  thf(d2_tsep_1, axiom,
% 1.76/1.95    (![A:$i]:
% 1.76/1.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.76/1.95       ( ![B:$i]:
% 1.76/1.95         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.76/1.95           ( ![C:$i]:
% 1.76/1.95             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.76/1.95               ( ![D:$i]:
% 1.76/1.95                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 1.76/1.95                     ( m1_pre_topc @ D @ A ) ) =>
% 1.76/1.95                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 1.76/1.95                     ( ( u1_struct_0 @ D ) =
% 1.76/1.95                       ( k2_xboole_0 @
% 1.76/1.95                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 1.76/1.95  thf('15', plain,
% 1.76/1.95      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.76/1.95         ((v2_struct_0 @ X13)
% 1.76/1.95          | ~ (m1_pre_topc @ X13 @ X14)
% 1.76/1.95          | (v2_struct_0 @ X15)
% 1.76/1.95          | ~ (v1_pre_topc @ X15)
% 1.76/1.95          | ~ (m1_pre_topc @ X15 @ X14)
% 1.76/1.95          | ((X15) != (k1_tsep_1 @ X14 @ X13 @ X16))
% 1.76/1.95          | ((u1_struct_0 @ X15)
% 1.76/1.95              = (k2_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))
% 1.76/1.95          | ~ (m1_pre_topc @ X16 @ X14)
% 1.76/1.95          | (v2_struct_0 @ X16)
% 1.76/1.95          | ~ (l1_pre_topc @ X14)
% 1.76/1.95          | (v2_struct_0 @ X14))),
% 1.76/1.95      inference('cnf', [status(esa)], [d2_tsep_1])).
% 1.76/1.95  thf('16', plain,
% 1.76/1.95      (![X13 : $i, X14 : $i, X16 : $i]:
% 1.76/1.95         ((v2_struct_0 @ X14)
% 1.76/1.95          | ~ (l1_pre_topc @ X14)
% 1.76/1.95          | (v2_struct_0 @ X16)
% 1.76/1.95          | ~ (m1_pre_topc @ X16 @ X14)
% 1.76/1.95          | ((u1_struct_0 @ (k1_tsep_1 @ X14 @ X13 @ X16))
% 1.76/1.95              = (k2_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))
% 1.76/1.95          | ~ (m1_pre_topc @ (k1_tsep_1 @ X14 @ X13 @ X16) @ X14)
% 1.76/1.95          | ~ (v1_pre_topc @ (k1_tsep_1 @ X14 @ X13 @ X16))
% 1.76/1.95          | (v2_struct_0 @ (k1_tsep_1 @ X14 @ X13 @ X16))
% 1.76/1.95          | ~ (m1_pre_topc @ X13 @ X14)
% 1.76/1.95          | (v2_struct_0 @ X13))),
% 1.76/1.95      inference('simplify', [status(thm)], ['15'])).
% 1.76/1.95  thf('17', plain,
% 1.76/1.95      (((v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.76/1.95        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | ~ (l1_pre_topc @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_A))),
% 1.76/1.95      inference('sup-', [status(thm)], ['14', '16'])).
% 1.76/1.95  thf('18', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('21', plain,
% 1.76/1.95      (((v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A))),
% 1.76/1.95      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 1.76/1.95  thf('22', plain,
% 1.76/1.95      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.76/1.95        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C))),
% 1.76/1.95      inference('simplify', [status(thm)], ['21'])).
% 1.76/1.95  thf('23', plain,
% 1.76/1.95      (((v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 1.76/1.95      inference('sup-', [status(thm)], ['7', '22'])).
% 1.76/1.95  thf('24', plain,
% 1.76/1.95      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.76/1.95        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C))),
% 1.76/1.95      inference('simplify', [status(thm)], ['23'])).
% 1.76/1.95  thf('25', plain,
% 1.76/1.95      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.76/1.95         (~ (m1_pre_topc @ X17 @ X18)
% 1.76/1.95          | (v2_struct_0 @ X17)
% 1.76/1.95          | ~ (l1_pre_topc @ X18)
% 1.76/1.95          | (v2_struct_0 @ X18)
% 1.76/1.95          | (v2_struct_0 @ X19)
% 1.76/1.95          | ~ (m1_pre_topc @ X19 @ X18)
% 1.76/1.95          | ~ (v2_struct_0 @ (k1_tsep_1 @ X18 @ X17 @ X19)))),
% 1.76/1.95      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.76/1.95  thf('26', plain,
% 1.76/1.95      (((v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.76/1.95        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | ~ (l1_pre_topc @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.76/1.95      inference('sup-', [status(thm)], ['24', '25'])).
% 1.76/1.95  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('30', plain,
% 1.76/1.95      (((v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B))),
% 1.76/1.95      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 1.76/1.95  thf('31', plain,
% 1.76/1.95      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C))),
% 1.76/1.95      inference('simplify', [status(thm)], ['30'])).
% 1.76/1.95  thf('32', plain,
% 1.76/1.95      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.95          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C))),
% 1.76/1.95      inference('simplify', [status(thm)], ['30'])).
% 1.76/1.95  thf('33', plain,
% 1.76/1.95      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf(d2_subset_1, axiom,
% 1.76/1.95    (![A:$i,B:$i]:
% 1.76/1.95     ( ( ( v1_xboole_0 @ A ) =>
% 1.76/1.95         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.76/1.95       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.76/1.95         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.76/1.95  thf('34', plain,
% 1.76/1.95      (![X8 : $i, X9 : $i]:
% 1.76/1.95         (~ (m1_subset_1 @ X8 @ X9)
% 1.76/1.95          | (r2_hidden @ X8 @ X9)
% 1.76/1.95          | (v1_xboole_0 @ X9))),
% 1.76/1.95      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.76/1.95  thf('35', plain,
% 1.76/1.95      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.76/1.95        | (r2_hidden @ sk_D_1 @ 
% 1.76/1.95           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.76/1.95      inference('sup-', [status(thm)], ['33', '34'])).
% 1.76/1.95  thf('36', plain,
% 1.76/1.95      (((r2_hidden @ sk_D_1 @ 
% 1.76/1.95         (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.76/1.95      inference('sup+', [status(thm)], ['32', '35'])).
% 1.76/1.95  thf(d3_xboole_0, axiom,
% 1.76/1.95    (![A:$i,B:$i,C:$i]:
% 1.76/1.95     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.76/1.95       ( ![D:$i]:
% 1.76/1.95         ( ( r2_hidden @ D @ C ) <=>
% 1.76/1.95           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.76/1.95  thf('37', plain,
% 1.76/1.95      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X4 @ X2)
% 1.76/1.95          | (r2_hidden @ X4 @ X3)
% 1.76/1.95          | (r2_hidden @ X4 @ X1)
% 1.76/1.95          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.76/1.95      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.76/1.95  thf('38', plain,
% 1.76/1.95      (![X1 : $i, X3 : $i, X4 : $i]:
% 1.76/1.95         ((r2_hidden @ X4 @ X1)
% 1.76/1.95          | (r2_hidden @ X4 @ X3)
% 1.76/1.95          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 1.76/1.95      inference('simplify', [status(thm)], ['37'])).
% 1.76/1.95  thf('39', plain,
% 1.76/1.95      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.76/1.95        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['36', '38'])).
% 1.76/1.95  thf('40', plain,
% 1.76/1.95      (((v1_xboole_0 @ 
% 1.76/1.95         (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.76/1.95        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B))),
% 1.76/1.95      inference('sup+', [status(thm)], ['31', '39'])).
% 1.76/1.95  thf('41', plain,
% 1.76/1.95      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.76/1.95        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (v1_xboole_0 @ 
% 1.76/1.95           (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 1.76/1.95      inference('simplify', [status(thm)], ['40'])).
% 1.76/1.95  thf(fc5_xboole_0, axiom,
% 1.76/1.95    (![A:$i,B:$i]:
% 1.76/1.95     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.76/1.95       ( ~( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) ))).
% 1.76/1.95  thf('42', plain,
% 1.76/1.95      (![X6 : $i, X7 : $i]:
% 1.76/1.95         ((v1_xboole_0 @ X6) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X7 @ X6)))),
% 1.76/1.95      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 1.76/1.95  thf('43', plain,
% 1.76/1.95      (((v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.76/1.95        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.76/1.95        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['41', '42'])).
% 1.76/1.95  thf(t1_subset, axiom,
% 1.76/1.95    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.76/1.95  thf('44', plain,
% 1.76/1.95      (![X11 : $i, X12 : $i]:
% 1.76/1.95         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 1.76/1.95      inference('cnf', [status(esa)], [t1_subset])).
% 1.76/1.95  thf('45', plain,
% 1.76/1.95      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 1.76/1.95        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['43', '44'])).
% 1.76/1.95  thf('46', plain,
% 1.76/1.95      (![X11 : $i, X12 : $i]:
% 1.76/1.95         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 1.76/1.95      inference('cnf', [status(esa)], [t1_subset])).
% 1.76/1.95  thf('47', plain,
% 1.76/1.95      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 1.76/1.95        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['45', '46'])).
% 1.76/1.95  thf('48', plain,
% 1.76/1.95      (![X20 : $i]:
% 1.76/1.95         (((X20) != (sk_D_1)) | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_C)))),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('49', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 1.76/1.95      inference('simplify', [status(thm)], ['48'])).
% 1.76/1.95  thf('50', plain,
% 1.76/1.95      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.76/1.95        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C))),
% 1.76/1.95      inference('sup-', [status(thm)], ['47', '49'])).
% 1.76/1.95  thf('51', plain,
% 1.76/1.95      (![X21 : $i]:
% 1.76/1.95         (((X21) != (sk_D_1)) | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_B)))),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('52', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))),
% 1.76/1.95      inference('simplify', [status(thm)], ['51'])).
% 1.76/1.95  thf('53', plain,
% 1.76/1.95      (((v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['50', '52'])).
% 1.76/1.95  thf('54', plain,
% 1.76/1.95      (![X9 : $i, X10 : $i]:
% 1.76/1.95         (~ (v1_xboole_0 @ X10)
% 1.76/1.95          | (m1_subset_1 @ X10 @ X9)
% 1.76/1.95          | ~ (v1_xboole_0 @ X9))),
% 1.76/1.95      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.76/1.95  thf('55', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 1.76/1.95      inference('simplify', [status(thm)], ['48'])).
% 1.76/1.95  thf('56', plain,
% 1.76/1.95      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_C)) | ~ (v1_xboole_0 @ sk_D_1))),
% 1.76/1.95      inference('sup-', [status(thm)], ['54', '55'])).
% 1.76/1.95  thf('57', plain,
% 1.76/1.95      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.76/1.95        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['36', '38'])).
% 1.76/1.95  thf('58', plain,
% 1.76/1.95      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('59', plain,
% 1.76/1.95      (![X9 : $i, X10 : $i]:
% 1.76/1.95         (~ (m1_subset_1 @ X10 @ X9)
% 1.76/1.95          | (v1_xboole_0 @ X10)
% 1.76/1.95          | ~ (v1_xboole_0 @ X9))),
% 1.76/1.95      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.76/1.95  thf('60', plain,
% 1.76/1.95      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.76/1.95        | (v1_xboole_0 @ sk_D_1))),
% 1.76/1.95      inference('sup-', [status(thm)], ['58', '59'])).
% 1.76/1.95  thf('61', plain,
% 1.76/1.95      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.76/1.95        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v1_xboole_0 @ sk_D_1))),
% 1.76/1.95      inference('sup-', [status(thm)], ['57', '60'])).
% 1.76/1.95  thf('62', plain,
% 1.76/1.95      (![X11 : $i, X12 : $i]:
% 1.76/1.95         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 1.76/1.95      inference('cnf', [status(esa)], [t1_subset])).
% 1.76/1.95  thf('63', plain,
% 1.76/1.95      (((v1_xboole_0 @ sk_D_1)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.76/1.95        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['61', '62'])).
% 1.76/1.95  thf('64', plain,
% 1.76/1.95      (![X11 : $i, X12 : $i]:
% 1.76/1.95         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 1.76/1.95      inference('cnf', [status(esa)], [t1_subset])).
% 1.76/1.95  thf('65', plain,
% 1.76/1.95      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.76/1.95        | (v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v1_xboole_0 @ sk_D_1)
% 1.76/1.95        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['63', '64'])).
% 1.76/1.95  thf('66', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 1.76/1.95      inference('simplify', [status(thm)], ['48'])).
% 1.76/1.95  thf('67', plain,
% 1.76/1.95      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.76/1.95        | (v1_xboole_0 @ sk_D_1)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_C))),
% 1.76/1.95      inference('sup-', [status(thm)], ['65', '66'])).
% 1.76/1.95  thf('68', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))),
% 1.76/1.95      inference('simplify', [status(thm)], ['51'])).
% 1.76/1.95  thf('69', plain,
% 1.76/1.95      (((v2_struct_0 @ sk_C)
% 1.76/1.95        | (v2_struct_0 @ sk_A)
% 1.76/1.95        | (v2_struct_0 @ sk_B)
% 1.76/1.95        | (v1_xboole_0 @ sk_D_1))),
% 1.76/1.95      inference('sup-', [status(thm)], ['67', '68'])).
% 1.76/1.95  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('71', plain,
% 1.76/1.95      (((v1_xboole_0 @ sk_D_1) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 1.76/1.95      inference('sup-', [status(thm)], ['69', '70'])).
% 1.76/1.95  thf('72', plain, (~ (v2_struct_0 @ sk_B)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('73', plain, (((v2_struct_0 @ sk_C) | (v1_xboole_0 @ sk_D_1))),
% 1.76/1.95      inference('clc', [status(thm)], ['71', '72'])).
% 1.76/1.95  thf('74', plain, (~ (v2_struct_0 @ sk_C)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('75', plain, ((v1_xboole_0 @ sk_D_1)),
% 1.76/1.95      inference('clc', [status(thm)], ['73', '74'])).
% 1.76/1.95  thf('76', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C))),
% 1.76/1.95      inference('demod', [status(thm)], ['56', '75'])).
% 1.76/1.95  thf('77', plain,
% 1.76/1.95      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 1.76/1.95      inference('sup-', [status(thm)], ['53', '76'])).
% 1.76/1.95  thf('78', plain, (~ (v2_struct_0 @ sk_B)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('79', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 1.76/1.95      inference('clc', [status(thm)], ['77', '78'])).
% 1.76/1.95  thf('80', plain, (~ (v2_struct_0 @ sk_C)),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('81', plain, ((v2_struct_0 @ sk_A)),
% 1.76/1.95      inference('clc', [status(thm)], ['79', '80'])).
% 1.76/1.95  thf('82', plain, ($false), inference('demod', [status(thm)], ['0', '81'])).
% 1.76/1.95  
% 1.76/1.95  % SZS output end Refutation
% 1.76/1.95  
% 1.76/1.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
