%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vHY5WIhhyt

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:11 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 311 expanded)
%              Number of leaves         :   22 (  95 expanded)
%              Depth                    :   28
%              Number of atoms          : 1151 (6306 expanded)
%              Number of equality atoms :   23 ( 250 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X17 @ X16 @ X18 ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X17 @ X16 @ X18 ) @ X17 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( X14
       != ( k1_tsep_1 @ X13 @ X12 @ X15 ) )
      | ( ( u1_struct_0 @ X14 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_pre_topc @ X15 @ X13 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X13 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X13 @ X12 @ X15 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X13 @ X12 @ X15 ) @ X13 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X13 @ X12 @ X15 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X13 @ X12 @ X15 ) )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v2_struct_0 @ X12 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X17 @ X16 @ X18 ) ) ) ),
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

thf('32',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X5
       != ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('38',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['31','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('42',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('44',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k2_xboole_0 @ X6 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( m1_subset_1 @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X19: $i] :
      ( ( X19 != sk_D_1 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X20: $i] :
      ( ( X20 != sk_D_1 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ( m1_subset_1 @ X11 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('62',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('63',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('65',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X11 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('74',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['0','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vHY5WIhhyt
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:40:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.51/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.70  % Solved by: fo/fo7.sh
% 0.51/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.70  % done 516 iterations in 0.246s
% 0.51/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.70  % SZS output start Refutation
% 0.51/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.70  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.51/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.70  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.51/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.51/0.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.51/0.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.70  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.51/0.70  thf(sk_B_type, type, sk_B: $i > $i).
% 0.51/0.70  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.51/0.70  thf(t16_tmap_1, conjecture,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.51/0.70           ( ![C:$i]:
% 0.51/0.70             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.70               ( ![D:$i]:
% 0.51/0.70                 ( ( m1_subset_1 @
% 0.51/0.70                     D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 0.51/0.70                   ( ~( ( ![E:$i]:
% 0.51/0.70                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.51/0.70                            ( ( E ) != ( D ) ) ) ) & 
% 0.51/0.70                        ( ![E:$i]:
% 0.51/0.70                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 0.51/0.70                            ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.70    (~( ![A:$i]:
% 0.51/0.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.51/0.70            ( l1_pre_topc @ A ) ) =>
% 0.51/0.70          ( ![B:$i]:
% 0.51/0.70            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.51/0.70              ( ![C:$i]:
% 0.51/0.70                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.70                  ( ![D:$i]:
% 0.51/0.70                    ( ( m1_subset_1 @
% 0.51/0.70                        D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 0.51/0.70                      ( ~( ( ![E:$i]:
% 0.51/0.70                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.51/0.70                               ( ( E ) != ( D ) ) ) ) & 
% 0.51/0.70                           ( ![E:$i]:
% 0.51/0.70                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 0.51/0.70                               ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.51/0.70    inference('cnf.neg', [status(esa)], [t16_tmap_1])).
% 0.51/0.70  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('2', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(dt_k1_tsep_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.51/0.70         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 0.51/0.70         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.70       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 0.51/0.70         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 0.51/0.70         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 0.51/0.70  thf('3', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.51/0.70         (~ (m1_pre_topc @ X16 @ X17)
% 0.51/0.70          | (v2_struct_0 @ X16)
% 0.51/0.70          | ~ (l1_pre_topc @ X17)
% 0.51/0.70          | (v2_struct_0 @ X17)
% 0.51/0.70          | (v2_struct_0 @ X18)
% 0.51/0.70          | ~ (m1_pre_topc @ X18 @ X17)
% 0.51/0.70          | (v1_pre_topc @ (k1_tsep_1 @ X17 @ X16 @ X18)))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.51/0.70  thf('4', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ X0))
% 0.51/0.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.51/0.70          | (v2_struct_0 @ X0)
% 0.51/0.70          | (v2_struct_0 @ sk_A)
% 0.51/0.70          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.70          | (v2_struct_0 @ sk_B_1))),
% 0.51/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.51/0.70  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('6', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ X0))
% 0.51/0.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.51/0.70          | (v2_struct_0 @ X0)
% 0.51/0.70          | (v2_struct_0 @ sk_A)
% 0.51/0.70          | (v2_struct_0 @ sk_B_1))),
% 0.51/0.70      inference('demod', [status(thm)], ['4', '5'])).
% 0.51/0.70  thf('7', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_B_1)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_C)
% 0.51/0.70        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['1', '6'])).
% 0.51/0.70  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('9', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('10', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.51/0.70         (~ (m1_pre_topc @ X16 @ X17)
% 0.51/0.70          | (v2_struct_0 @ X16)
% 0.51/0.70          | ~ (l1_pre_topc @ X17)
% 0.51/0.70          | (v2_struct_0 @ X17)
% 0.51/0.70          | (v2_struct_0 @ X18)
% 0.51/0.70          | ~ (m1_pre_topc @ X18 @ X17)
% 0.51/0.70          | (m1_pre_topc @ (k1_tsep_1 @ X17 @ X16 @ X18) @ X17))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.51/0.70  thf('11', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ X0) @ sk_A)
% 0.51/0.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.51/0.70          | (v2_struct_0 @ X0)
% 0.51/0.70          | (v2_struct_0 @ sk_A)
% 0.51/0.70          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.70          | (v2_struct_0 @ sk_B_1))),
% 0.51/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.70  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('13', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ X0) @ sk_A)
% 0.51/0.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.51/0.70          | (v2_struct_0 @ X0)
% 0.51/0.70          | (v2_struct_0 @ sk_A)
% 0.51/0.70          | (v2_struct_0 @ sk_B_1))),
% 0.51/0.70      inference('demod', [status(thm)], ['11', '12'])).
% 0.51/0.70  thf('14', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_B_1)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_C)
% 0.51/0.70        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C) @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['8', '13'])).
% 0.51/0.70  thf(d2_tsep_1, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.51/0.70           ( ![C:$i]:
% 0.51/0.70             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.70               ( ![D:$i]:
% 0.51/0.70                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.51/0.70                     ( m1_pre_topc @ D @ A ) ) =>
% 0.51/0.70                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 0.51/0.70                     ( ( u1_struct_0 @ D ) =
% 0.51/0.70                       ( k2_xboole_0 @
% 0.51/0.70                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.70  thf('15', plain,
% 0.51/0.70      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.51/0.70         ((v2_struct_0 @ X12)
% 0.51/0.70          | ~ (m1_pre_topc @ X12 @ X13)
% 0.51/0.70          | (v2_struct_0 @ X14)
% 0.51/0.70          | ~ (v1_pre_topc @ X14)
% 0.51/0.70          | ~ (m1_pre_topc @ X14 @ X13)
% 0.51/0.70          | ((X14) != (k1_tsep_1 @ X13 @ X12 @ X15))
% 0.51/0.70          | ((u1_struct_0 @ X14)
% 0.51/0.70              = (k2_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X15)))
% 0.51/0.70          | ~ (m1_pre_topc @ X15 @ X13)
% 0.51/0.70          | (v2_struct_0 @ X15)
% 0.51/0.70          | ~ (l1_pre_topc @ X13)
% 0.51/0.70          | (v2_struct_0 @ X13))),
% 0.51/0.70      inference('cnf', [status(esa)], [d2_tsep_1])).
% 0.51/0.70  thf('16', plain,
% 0.51/0.70      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.51/0.70         ((v2_struct_0 @ X13)
% 0.51/0.70          | ~ (l1_pre_topc @ X13)
% 0.51/0.70          | (v2_struct_0 @ X15)
% 0.51/0.70          | ~ (m1_pre_topc @ X15 @ X13)
% 0.51/0.70          | ((u1_struct_0 @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 0.51/0.70              = (k2_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X15)))
% 0.51/0.70          | ~ (m1_pre_topc @ (k1_tsep_1 @ X13 @ X12 @ X15) @ X13)
% 0.51/0.70          | ~ (v1_pre_topc @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 0.51/0.70          | (v2_struct_0 @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 0.51/0.70          | ~ (m1_pre_topc @ X12 @ X13)
% 0.51/0.70          | (v2_struct_0 @ X12))),
% 0.51/0.70      inference('simplify', [status(thm)], ['15'])).
% 0.51/0.70  thf('17', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_C)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.51/0.70        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_C)
% 0.51/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['14', '16'])).
% 0.51/0.70  thf('18', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('21', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_C)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.51/0.70        | (v2_struct_0 @ sk_C)
% 0.51/0.70        | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.51/0.70  thf('22', plain,
% 0.51/0.70      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70          = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.51/0.70        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_C))),
% 0.51/0.70      inference('simplify', [status(thm)], ['21'])).
% 0.51/0.70  thf('23', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_C)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | (v2_struct_0 @ sk_C)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))),
% 0.51/0.70      inference('sup-', [status(thm)], ['7', '22'])).
% 0.51/0.70  thf('24', plain,
% 0.51/0.70      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70          = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.51/0.70        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_C))),
% 0.51/0.70      inference('simplify', [status(thm)], ['23'])).
% 0.51/0.70  thf('25', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.51/0.70         (~ (m1_pre_topc @ X16 @ X17)
% 0.51/0.70          | (v2_struct_0 @ X16)
% 0.51/0.70          | ~ (l1_pre_topc @ X17)
% 0.51/0.70          | (v2_struct_0 @ X17)
% 0.51/0.70          | (v2_struct_0 @ X18)
% 0.51/0.70          | ~ (m1_pre_topc @ X18 @ X17)
% 0.51/0.70          | ~ (v2_struct_0 @ (k1_tsep_1 @ X17 @ X16 @ X18)))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.51/0.70  thf('26', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_C)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.51/0.70        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_C)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | ~ (m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.70  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('29', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('30', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_C)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.51/0.70        | (v2_struct_0 @ sk_C)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_B_1))),
% 0.51/0.70      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.51/0.70  thf('31', plain,
% 0.51/0.70      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70          = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_C))),
% 0.51/0.70      inference('simplify', [status(thm)], ['30'])).
% 0.51/0.70  thf('32', plain,
% 0.51/0.70      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.51/0.70          = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_C))),
% 0.51/0.70      inference('simplify', [status(thm)], ['30'])).
% 0.51/0.70  thf('33', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.51/0.70        (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(d2_subset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( v1_xboole_0 @ A ) =>
% 0.51/0.70         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.51/0.70       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.51/0.70         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.70  thf('34', plain,
% 0.51/0.70      (![X9 : $i, X10 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X9 @ X10)
% 0.51/0.70          | (r2_hidden @ X9 @ X10)
% 0.51/0.70          | (v1_xboole_0 @ X10))),
% 0.51/0.70      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.51/0.70  thf('35', plain,
% 0.51/0.70      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))
% 0.51/0.70        | (r2_hidden @ sk_D_1 @ 
% 0.51/0.70           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))))),
% 0.51/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.51/0.70  thf('36', plain,
% 0.51/0.70      (((r2_hidden @ sk_D_1 @ 
% 0.51/0.70         (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.51/0.70        | (v2_struct_0 @ sk_C)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))))),
% 0.51/0.70      inference('sup+', [status(thm)], ['32', '35'])).
% 0.51/0.70  thf(d3_xboole_0, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.51/0.70       ( ![D:$i]:
% 0.51/0.70         ( ( r2_hidden @ D @ C ) <=>
% 0.51/0.70           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.51/0.70  thf('37', plain,
% 0.51/0.70      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X7 @ X5)
% 0.51/0.70          | (r2_hidden @ X7 @ X6)
% 0.51/0.70          | (r2_hidden @ X7 @ X4)
% 0.51/0.70          | ((X5) != (k2_xboole_0 @ X6 @ X4)))),
% 0.51/0.70      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.51/0.70  thf('38', plain,
% 0.51/0.70      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.51/0.70         ((r2_hidden @ X7 @ X4)
% 0.51/0.70          | (r2_hidden @ X7 @ X6)
% 0.51/0.70          | ~ (r2_hidden @ X7 @ (k2_xboole_0 @ X6 @ X4)))),
% 0.51/0.70      inference('simplify', [status(thm)], ['37'])).
% 0.51/0.70  thf('39', plain,
% 0.51/0.70      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_C)
% 0.51/0.70        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.51/0.70        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['36', '38'])).
% 0.51/0.70  thf('40', plain,
% 0.51/0.70      (((v1_xboole_0 @ 
% 0.51/0.70         (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.51/0.70        | (v2_struct_0 @ sk_C)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_B_1)
% 0.51/0.70        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.51/0.70        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.51/0.70        | (v2_struct_0 @ sk_C)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_B_1))),
% 0.51/0.70      inference('sup+', [status(thm)], ['31', '39'])).
% 0.51/0.70  thf('41', plain,
% 0.51/0.71      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.51/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.51/0.71        | (v2_struct_0 @ sk_B_1)
% 0.51/0.71        | (v2_struct_0 @ sk_A)
% 0.51/0.71        | (v2_struct_0 @ sk_C)
% 0.51/0.71        | (v1_xboole_0 @ 
% 0.51/0.71           (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))),
% 0.51/0.71      inference('simplify', [status(thm)], ['40'])).
% 0.51/0.71  thf(d1_xboole_0, axiom,
% 0.51/0.71    (![A:$i]:
% 0.51/0.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.71  thf('42', plain,
% 0.51/0.71      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.51/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.71  thf('43', plain,
% 0.51/0.71      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X3 @ X4)
% 0.51/0.71          | (r2_hidden @ X3 @ X5)
% 0.51/0.71          | ((X5) != (k2_xboole_0 @ X6 @ X4)))),
% 0.51/0.71      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.51/0.71  thf('44', plain,
% 0.51/0.71      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.51/0.71         ((r2_hidden @ X3 @ (k2_xboole_0 @ X6 @ X4)) | ~ (r2_hidden @ X3 @ X4))),
% 0.51/0.71      inference('simplify', [status(thm)], ['43'])).
% 0.51/0.71  thf('45', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((v1_xboole_0 @ X0)
% 0.51/0.71          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['42', '44'])).
% 0.51/0.71  thf('46', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.71  thf('47', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.51/0.71  thf('48', plain,
% 0.51/0.71      (((v2_struct_0 @ sk_C)
% 0.51/0.71        | (v2_struct_0 @ sk_A)
% 0.51/0.71        | (v2_struct_0 @ sk_B_1)
% 0.51/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.51/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.51/0.71        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['41', '47'])).
% 0.51/0.71  thf('49', plain,
% 0.51/0.71      (![X9 : $i, X10 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X9 @ X10)
% 0.51/0.71          | (m1_subset_1 @ X9 @ X10)
% 0.51/0.71          | (v1_xboole_0 @ X10))),
% 0.51/0.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.51/0.71  thf('50', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.71  thf('51', plain,
% 0.51/0.71      (![X9 : $i, X10 : $i]:
% 0.51/0.71         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.51/0.71      inference('clc', [status(thm)], ['49', '50'])).
% 0.51/0.71  thf('52', plain,
% 0.51/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.51/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.51/0.71        | (v2_struct_0 @ sk_B_1)
% 0.51/0.71        | (v2_struct_0 @ sk_A)
% 0.51/0.71        | (v2_struct_0 @ sk_C)
% 0.51/0.71        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['48', '51'])).
% 0.51/0.71  thf('53', plain,
% 0.51/0.71      (![X9 : $i, X10 : $i]:
% 0.51/0.71         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.51/0.71      inference('clc', [status(thm)], ['49', '50'])).
% 0.51/0.71  thf('54', plain,
% 0.51/0.71      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.51/0.71        | (v2_struct_0 @ sk_C)
% 0.51/0.71        | (v2_struct_0 @ sk_A)
% 0.51/0.71        | (v2_struct_0 @ sk_B_1)
% 0.51/0.71        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.51/0.71        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['52', '53'])).
% 0.51/0.71  thf('55', plain,
% 0.51/0.71      (![X19 : $i]:
% 0.51/0.71         (((X19) != (sk_D_1)) | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ sk_C)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('56', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 0.51/0.71      inference('simplify', [status(thm)], ['55'])).
% 0.51/0.71  thf('57', plain,
% 0.51/0.71      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.51/0.71        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.51/0.71        | (v2_struct_0 @ sk_B_1)
% 0.51/0.71        | (v2_struct_0 @ sk_A)
% 0.51/0.71        | (v2_struct_0 @ sk_C))),
% 0.51/0.71      inference('sup-', [status(thm)], ['54', '56'])).
% 0.51/0.71  thf('58', plain,
% 0.51/0.71      (![X20 : $i]:
% 0.51/0.71         (((X20) != (sk_D_1)) | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B_1)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('59', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1))),
% 0.51/0.71      inference('simplify', [status(thm)], ['58'])).
% 0.51/0.71  thf('60', plain,
% 0.51/0.71      (((v2_struct_0 @ sk_C)
% 0.51/0.71        | (v2_struct_0 @ sk_A)
% 0.51/0.71        | (v2_struct_0 @ sk_B_1)
% 0.51/0.71        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['57', '59'])).
% 0.51/0.71  thf('61', plain,
% 0.51/0.71      (![X10 : $i, X11 : $i]:
% 0.51/0.71         (~ (v1_xboole_0 @ X11)
% 0.51/0.71          | (m1_subset_1 @ X11 @ X10)
% 0.51/0.71          | ~ (v1_xboole_0 @ X10))),
% 0.51/0.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.51/0.71  thf('62', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 0.51/0.71      inference('simplify', [status(thm)], ['55'])).
% 0.51/0.71  thf('63', plain,
% 0.51/0.71      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_C)) | ~ (v1_xboole_0 @ sk_D_1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['61', '62'])).
% 0.51/0.71  thf('64', plain,
% 0.51/0.71      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))
% 0.51/0.71        | (v2_struct_0 @ sk_B_1)
% 0.51/0.71        | (v2_struct_0 @ sk_A)
% 0.51/0.71        | (v2_struct_0 @ sk_C)
% 0.51/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.51/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['36', '38'])).
% 0.51/0.71  thf('65', plain,
% 0.51/0.71      ((m1_subset_1 @ sk_D_1 @ 
% 0.51/0.71        (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('66', plain,
% 0.51/0.71      (![X10 : $i, X11 : $i]:
% 0.51/0.71         (~ (m1_subset_1 @ X11 @ X10)
% 0.51/0.71          | (v1_xboole_0 @ X11)
% 0.51/0.71          | ~ (v1_xboole_0 @ X10))),
% 0.51/0.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.51/0.71  thf('67', plain,
% 0.51/0.71      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))
% 0.51/0.71        | (v1_xboole_0 @ sk_D_1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['65', '66'])).
% 0.51/0.71  thf('68', plain,
% 0.51/0.71      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.51/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.51/0.71        | (v2_struct_0 @ sk_C)
% 0.51/0.71        | (v2_struct_0 @ sk_A)
% 0.51/0.71        | (v2_struct_0 @ sk_B_1)
% 0.51/0.71        | (v1_xboole_0 @ sk_D_1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['64', '67'])).
% 0.51/0.71  thf('69', plain,
% 0.51/0.71      (![X9 : $i, X10 : $i]:
% 0.51/0.71         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.51/0.71      inference('clc', [status(thm)], ['49', '50'])).
% 0.51/0.71  thf('70', plain,
% 0.51/0.71      (((v1_xboole_0 @ sk_D_1)
% 0.51/0.71        | (v2_struct_0 @ sk_B_1)
% 0.51/0.71        | (v2_struct_0 @ sk_A)
% 0.51/0.71        | (v2_struct_0 @ sk_C)
% 0.51/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.51/0.71        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['68', '69'])).
% 0.51/0.71  thf('71', plain,
% 0.51/0.71      (![X9 : $i, X10 : $i]:
% 0.51/0.71         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.51/0.71      inference('clc', [status(thm)], ['49', '50'])).
% 0.51/0.71  thf('72', plain,
% 0.51/0.71      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.51/0.71        | (v2_struct_0 @ sk_C)
% 0.51/0.71        | (v2_struct_0 @ sk_A)
% 0.51/0.71        | (v2_struct_0 @ sk_B_1)
% 0.51/0.71        | (v1_xboole_0 @ sk_D_1)
% 0.51/0.71        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['70', '71'])).
% 0.51/0.71  thf('73', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 0.51/0.71      inference('simplify', [status(thm)], ['55'])).
% 0.51/0.71  thf('74', plain,
% 0.51/0.71      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.51/0.71        | (v1_xboole_0 @ sk_D_1)
% 0.51/0.71        | (v2_struct_0 @ sk_B_1)
% 0.51/0.71        | (v2_struct_0 @ sk_A)
% 0.51/0.71        | (v2_struct_0 @ sk_C))),
% 0.51/0.71      inference('sup-', [status(thm)], ['72', '73'])).
% 0.51/0.71  thf('75', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1))),
% 0.51/0.71      inference('simplify', [status(thm)], ['58'])).
% 0.51/0.71  thf('76', plain,
% 0.51/0.71      (((v2_struct_0 @ sk_C)
% 0.51/0.71        | (v2_struct_0 @ sk_A)
% 0.51/0.71        | (v2_struct_0 @ sk_B_1)
% 0.51/0.71        | (v1_xboole_0 @ sk_D_1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['74', '75'])).
% 0.51/0.71  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('78', plain,
% 0.51/0.71      (((v1_xboole_0 @ sk_D_1) | (v2_struct_0 @ sk_B_1) | (v2_struct_0 @ sk_C))),
% 0.51/0.71      inference('sup-', [status(thm)], ['76', '77'])).
% 0.51/0.71  thf('79', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('80', plain, (((v2_struct_0 @ sk_C) | (v1_xboole_0 @ sk_D_1))),
% 0.51/0.71      inference('clc', [status(thm)], ['78', '79'])).
% 0.51/0.71  thf('81', plain, (~ (v2_struct_0 @ sk_C)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('82', plain, ((v1_xboole_0 @ sk_D_1)),
% 0.51/0.71      inference('clc', [status(thm)], ['80', '81'])).
% 0.51/0.71  thf('83', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C))),
% 0.51/0.71      inference('demod', [status(thm)], ['63', '82'])).
% 0.51/0.71  thf('84', plain,
% 0.51/0.71      (((v2_struct_0 @ sk_B_1) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.51/0.71      inference('sup-', [status(thm)], ['60', '83'])).
% 0.51/0.71  thf('85', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('86', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.51/0.71      inference('clc', [status(thm)], ['84', '85'])).
% 0.51/0.71  thf('87', plain, (~ (v2_struct_0 @ sk_C)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('88', plain, ((v2_struct_0 @ sk_A)),
% 0.51/0.71      inference('clc', [status(thm)], ['86', '87'])).
% 0.51/0.71  thf('89', plain, ($false), inference('demod', [status(thm)], ['0', '88'])).
% 0.51/0.71  
% 0.51/0.71  % SZS output end Refutation
% 0.51/0.71  
% 0.51/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
